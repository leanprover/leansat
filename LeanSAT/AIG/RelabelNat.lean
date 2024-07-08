/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.AIG.Relabel

open Std

variable {α : Type} [BEq α] [Hashable α]

-- TODO: auxiliary theorem, possibly upstream
theorem _root_.Array.get_of_mem {a : α} {as : Array α}
    : a ∈ as → (∃ (i : Fin as.size), as[i] = a) := by
  intro ha
  rcases List.get_of_mem ha.val with ⟨i, hi⟩
  exists i

namespace AIG
namespace RelabelNat
namespace State

/--
This invariant ensures that we only insert an atom at most once and with a monotonically increasing
index.
-/
inductive Inv1 : Nat → HashMap α Nat → Prop where
| empty : Inv1 0 {}
| insert (hinv : Inv1 n map) (hfind : map[x]? = none) : Inv1 (n + 1) (map.insert x n)

/--
Proof sketch for this axiom once we have more `HashMap` theory:
```
  induction hinv generalizing m with
  | empty =>
    -- contradiction, can't find anything in empty hashmaps
    sorry
  | insert hinv hnone ih =>
    -- here we have a find? (insert) = some . We do a case split on wehther we found the element
    -- in the original hashmap or in the new one.
    -- 1. original: ih closes the goal
    -- 2. new one: the new element is the same in both cases
    sorry
```
-/
axiom Inv1.property {n m : Nat} (x y : α) (map : HashMap α Nat) (hinv : Inv1 n map)
    (hfound1 : map[x]? = some m) (hfound2 : map[y]? = some m) : x = y

/--
This invariant says that we have already visited and inserted all nodes up to a certain index.
-/
inductive Inv2 (decls : Array (Decl α)) : Nat → HashMap α Nat → Prop where
| empty : Inv2 decls 0 {}
| newAtom (hinv : Inv2 decls idx map) (hlt : idx < decls.size) (hatom : decls[idx] = .atom a)
  (hmap : map[a]? = none)
  : Inv2 decls (idx + 1) (map.insert a val)
| oldAtom (hinv : Inv2 decls idx map) (hlt : idx < decls.size) (hatom : decls[idx] = .atom a)
  (hmap : map[a]? = some n)
  : Inv2 decls (idx + 1) map
| const (hinv : Inv2 decls idx map) (hlt : idx < decls.size) (hatom : decls[idx] = .const b)
  : Inv2 decls (idx + 1) map
| gate (hinv : Inv2 decls idx map) (hlt : idx < decls.size) (hatom : decls[idx] = .gate l r li ri)
  : Inv2 decls (idx + 1) map

-- TODO: Think about merging Inv1 and Inv2, they are *very* close.

theorem Inv2.upper_lt_size {decls : Array (Decl α)} (hinv : Inv2 decls upper map)
    : upper ≤ decls.size := by
  cases hinv <;> omega

/--
The key property provided by `Inv2`, if we have `Inv2` at a certain index, then all atoms below
that index have been inserted into the `HashMap`.
-/
axiom Inv2.property (decls : Array (Decl α)) (idx upper : Nat) (map : HashMap α Nat)
    (hinv : Inv2 decls upper map)
    : ∀ (hidx : idx < upper), ∀ (a : α),
        decls[idx]'(by have := upper_lt_size hinv; omega) = .atom a
          → ∃ n, map[a]? = some n

end State

/--
The invariant carrying state structure for building the `HashMap` that translates from arbitrary
atom identifiers to `Nat`.
-/
structure State (α : Type) [BEq α] [Hashable α] (decls : Array (Decl α)) (idx : Nat) where
  /--
  The next number to use for identifying an atom.
  -/
  max : Nat
  /--
  The translation `HashMap`
  -/
  map : HashMap α Nat
  /--
  Proof that we never reuse a number.
  -/
  inv1 : State.Inv1 max map
  /--
  Proof that we inserted all atoms until `idx`.
  -/
  inv2 : State.Inv2 decls idx map

namespace State

/--
The basic initial state.
-/
def empty {decls : Array (Decl α)} : State α decls 0 :=
  { max := 0, map := {}, inv1 := Inv1.empty, inv2 := Inv2.empty }

/--
Insert a `Decl.atom` into the `State` structure.
-/
def addAtom {decls : Array (Decl α)} {hidx} (state : State α decls idx) (a : α)
    (h : decls[idx]'hidx = .atom a)
    : State α decls (idx + 1) :=
  match hmap:state.map[a]? with
  | some _ =>
    { state with
        inv2 := by
          apply Inv2.oldAtom
          . exact state.inv2
          . assumption
          . assumption
    }
  | none =>
    {
      max := state.max + 1
      map := state.map.insert a state.max
      inv1 := by
        apply State.Inv1.insert
        . exact state.inv1
        . assumption
      inv2 := by
        apply Inv2.newAtom
        . exact state.inv2
        . assumption
        . assumption
    }

/--
Insert a `Decl.const` into the `State` structure.
-/
def addConst {decls : Array (Decl α)} {hidx} (state : State α decls idx) (b : Bool)
    (h : decls[idx]'hidx = .const b)
    : State α decls (idx + 1) :=
  { state with
      inv2 := by
        apply Inv2.const
        . exact state.inv2
        . assumption
  }

/--
Insert a `Decl.gate` into the `State` structure.
-/
def addGate {decls : Array (Decl α)} {hidx} (state : State α decls idx) (lhs rhs : Nat)
    (linv rinv : Bool) (h : decls[idx]'hidx = .gate lhs rhs linv rinv)
    : State α decls (idx + 1) :=
  { state with
      inv2 := by
        apply Inv2.gate
        . exact state.inv2
        . assumption
  }

/--
Build up a `State` that has all atoms of an `AIG` inserted.
-/
def ofAIGAux (aig : AIG α) : State α aig.decls aig.decls.size :=
  go aig.decls 0 .empty
where
  go (decls : Array (Decl α)) (idx : Nat) (state : State α decls idx) : State α decls decls.size :=
    if hidx:idx < decls.size then
      let decl := decls[idx]
      match hdecl:decl with
      | .atom a => go decls (idx + 1) (state.addAtom a hdecl)
      | .const b => go decls (idx + 1) (state.addConst b hdecl)
      | .gate lhs rhs linv rinv => go decls (idx + 1) (state.addGate lhs rhs linv rinv hdecl)
    else
      have : idx = decls.size := by
        have := state.inv2.upper_lt_size
        omega
      this ▸ state
  termination_by decls.size - idx

/--
Obtain the atom mapping from α to `Nat` for a given `AIG`.
-/
def ofAIG (aig : AIG α) : HashMap α Nat :=
  ofAIGAux aig |>.map

/--
The map returned by `ofAIG` fulfills the `Inv1` property.
-/
theorem ofAIG.Inv1 (aig : AIG α) : ∃ n, Inv1 n (ofAIG aig) := by
  exists (ofAIGAux aig).max
  dsimp [ofAIG]
  exact (ofAIGAux aig).inv1

/--
The map returned by `ofAIG` fulfills the `Inv2` property.
-/
theorem ofAIG.Inv2 (aig : AIG α) : Inv2 aig.decls aig.decls.size (ofAIG aig) := by
  have := (ofAIGAux aig).inv2
  simp [ofAIG, this]

/--
Assuming that we find a `Nat` for an atom in the `ofAIG` map, that `Nat` is unique in the map.
-/
theorem ofAIG_find_unique {aig : AIG α} (a : α) (ha : (ofAIG aig)[a]? = some n)
    : ∀ a', (ofAIG aig)[a']? = some n → a = a' := by
  intro a' ha'
  rcases ofAIG.Inv1 aig with ⟨n, hn⟩
  apply Inv1.property <;> assumption

/--
We will find a `Nat` for every atom in the `AIG` that the `ofAIG` map was built from.
-/
theorem ofAIG_find_some {aig : AIG α} : ∀ a ∈ aig, ∃ n, (ofAIG aig)[a]? = some n := by
  intro a ha
  simp only [mem_def] at ha
  rcases Array.get_of_mem ha with ⟨⟨i, isLt⟩, hi⟩
  apply Inv2.property
  . assumption
  . exact aig.decls.size
  . apply ofAIG.Inv2
  . omega

end State
end RelabelNat

def relabelNat' (aig : AIG α) : (AIG Nat × HashMap α Nat) :=
  let map := RelabelNat.State.ofAIG aig
  let aig := aig.relabel fun x =>
    -- The none branch never gets hit, we prove this below
    match map[x]? with
    | some var => var
    | none => 0
  (aig, map)

/--
Map an `AIG` with arbitrary atom identifiers to one that uses `Nat` as atom identifiers. This is
useful for preparing an `AIG` for CNF translation if it doesn't already use `Nat` identifiers.
-/
def relabelNat (aig : AIG α) : AIG Nat :=
  relabelNat' aig |>.fst

@[simp]
theorem relabelNat'_fst_eq_relabelNat {aig : AIG α} : aig.relabelNat'.fst = aig.relabelNat := by
  rfl

@[simp]
theorem relabelNat_size_eq_size {aig : AIG α} : aig.relabelNat.decls.size = aig.decls.size := by
  simp [relabelNat, relabelNat']

/--
`relabelNat` preserves unsatisfiablility.
-/
theorem relabelNat_unsat_iff [Nonempty α] {aig : AIG α} {hidx1} {hidx2}
    : (aig.relabelNat).unsatAt idx hidx1 ↔ aig.unsatAt idx hidx2 := by
  dsimp [relabelNat, relabelNat']
  rw [relabel_unsat_iff]
  intro x y hx hy heq
  split at heq
  . next hcase1 =>
    split at heq
    . next hcase2 =>
      apply RelabelNat.State.ofAIG_find_unique
      . assumption
      . rw [heq]
        assumption
    . next hcase2 =>
      exfalso
      rcases RelabelNat.State.ofAIG_find_some y hy with ⟨n, hn⟩
      simp[hcase2] at hn
  . next hcase =>
    exfalso
    rcases RelabelNat.State.ofAIG_find_some x hx with ⟨n, hn⟩
    simp[hcase] at hn

namespace Entrypoint

def relabelNat' (entry : Entrypoint α) : (Entrypoint Nat × HashMap α Nat) :=
  let res := entry.aig.relabelNat'
  let entry := { entry with
      aig := res.fst,
      ref.hgate := by simp [entry.ref.hgate, res]
  }
  (entry, res.snd)

/--
Map an `Entrypoint` with arbitrary atom identifiers to one that uses `Nat` as atom identifiers.
This is useful for preparing an `AIG` for CNF translation if it doesn't already use `Nat`
identifiers.
-/
def relabelNat (entry : Entrypoint α) : Entrypoint Nat :=
  { entry with
      aig := entry.aig.relabelNat
      ref.hgate := by simp[entry.ref.hgate]
  }

/--
`relabelNat` preserves unsatisfiablility.
-/
theorem relabelNat_unsat_iff {entry : Entrypoint α} [Nonempty α]
    : (entry.relabelNat).unsat ↔ entry.unsat:= by
  simp [relabelNat, unsat]
  rw [AIG.relabelNat_unsat_iff]

end Entrypoint
end AIG

