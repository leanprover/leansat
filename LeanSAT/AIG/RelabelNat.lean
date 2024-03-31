import LeanSAT.AIG.Relabel

open Std

variable {α : Type} [BEq α] [Hashable α]

namespace AIG

namespace RelabelNat

inductive State.Inv1 : Nat → HashMap α Nat → Prop where
| empty : Inv1 0 {}
| insert (hinv : Inv1 n map) (hfind : map.find? x = none) : Inv1 (n + 1) (map.insert x n)

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
axiom State.Inv1.property {n m : Nat} (x y : α) (map : HashMap α Nat) (hinv : State.Inv1 n map)
    (hfound1 : map.find? x = some m) (hfound2 : map.find? y = some m) : x = y

inductive State.Inv2 (decls : Array (Decl α)) : Nat → HashMap α Nat → Prop where
| empty : Inv2 decls 0 {}
| newAtom (hinv : Inv2 decls idx map) (hlt : idx < decls.size) (hatom : decls[idx] = .atom a)
  (hmap : map.find? a = none)
  : Inv2 decls (idx + 1) (map.insert a val)
| oldAtom (hinv : Inv2 decls idx map) (hlt : idx < decls.size) (hatom : decls[idx] = .atom a)
  (hmap : map.find? a = some n)
  : Inv2 decls (idx + 1) map
| const (hinv : Inv2 decls idx map) (hlt : idx < decls.size) (hatom : decls[idx] = .const b)
  : Inv2 decls (idx + 1) map
| gate (hinv : Inv2 decls idx map) (hlt : idx < decls.size) (hatom : decls[idx] = .gate l r li ri)
  : Inv2 decls (idx + 1) map

theorem State.Inv2.upper_lt_size {decls : Array (Decl α)} (hinv : Inv2 decls upper map)
    : upper ≤ decls.size := by
  cases hinv <;> omega

axiom State.Inv2.property (decls : Array (Decl α)) (idx upper : Nat) (map : HashMap α Nat)
    (hinv : Inv2 decls upper map)
    : ∀ (hidx : idx < upper), ∀ (a : α),
        decls[idx]'(by have := upper_lt_size hinv; omega) = .atom a
          → ∃ n, map.find? a = some n

structure State (α : Type) [BEq α] [Hashable α] (decls : Array (Decl α)) (idx : Nat) where
  max : Nat
  map : HashMap α Nat
  inv1 : State.Inv1 max map
  inv2 : State.Inv2 decls idx map

def State.empty {decls : Array (Decl α)} : State α decls 0 :=
  { max := 0, map := {}, inv1 := State.Inv1.empty, inv2 := State.Inv2.empty }

def State.addVar {decls : Array (Decl α)} (state : State α decls idx) (a : α)
    (h : decls[idx]'sorry = .atom a)
    : State α decls (idx + 1) :=
  match hmap:state.map.find? a with
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

def State.addConst {decls : Array (Decl α)} (state : State α decls idx) (b : Bool)
    (h : decls[idx]'sorry = .const b)
    : State α decls (idx + 1) :=
  { state with
      inv2 := by
        apply Inv2.const
        . exact state.inv2
        . assumption
  }

def State.addGate {decls : Array (Decl α)} (state : State α decls idx) (lhs rhs : Nat)
    (linv rinv : Bool) (h : decls[idx]'sorry = .gate lhs rhs linv rinv)
    : State α decls (idx + 1) :=
  { state with
      inv2 := by
        apply Inv2.gate
        . exact state.inv2
        . assumption
  }

def State.ofAIGAux (aig : AIG α) : State α aig.decls aig.decls.size :=
  go aig.decls 0 State.empty
where
  go (decls : Array (Decl α)) (idx : Nat) (state : State α decls idx) : State α decls decls.size :=
    if hidx:idx < decls.size then
      let decl := decls[idx]
      match hdecl:decl with
      | .atom a => go decls (idx + 1) (state.addVar a hdecl)
      | .const b => go decls (idx + 1) (state.addConst b hdecl)
      | .gate lhs rhs linv rinv => go decls (idx + 1) (state.addGate lhs rhs linv rinv hdecl)
    else
      have : idx = decls.size := by
        have := state.inv2.upper_lt_size
        omega
      this ▸ state
  termination_by decls.size - idx

def State.ofAIG (aig : AIG α) : HashMap α Nat :=
  State.ofAIGAux aig |>.map

theorem State.ofAIG.Inv1 (aig : AIG α) : ∃ n, State.Inv1 n (State.ofAIG aig) := by
  exists (State.ofAIGAux aig).max
  dsimp [ofAIG]
  exact (State.ofAIGAux aig).inv1

theorem State.ofAIG.Inv2 (aig : AIG α) : State.Inv2 aig.decls aig.decls.size (State.ofAIG aig) := by
  have := (State.ofAIGAux aig).inv2
  simp [State.ofAIG, this]

-- TODO: auxiliary theorem, possibly upstream
theorem _root_.Array.get_of_mem {a : α} {as : Array α}
    : a ∈ as → (∃ (i : Fin as.size), as[i] = a) := by
  intro ha
  rcases List.get_of_mem ha.val with ⟨i, hi⟩
  exists i

theorem State.ofAIG_find_some {aig : AIG α} : ∀ a ∈ aig, ∃ n, (State.ofAIG aig).find? a = some n := by
  intro a ha
  simp only [mem_def] at ha
  rcases Array.get_of_mem ha with ⟨⟨i, isLt⟩, hi⟩
  apply Inv2.property
  . assumption
  . exact aig.decls.size
  . apply ofAIG.Inv2
  . omega

theorem State.ofAIG_find_unique {aig : AIG α} (a : α) (ha : (State.ofAIG aig).find? a = some n)
    : ∀ a', (State.ofAIG aig).find? a' = some n → a = a' := by
  intro a' ha'
  rcases State.ofAIG.Inv1 aig with ⟨n, hn⟩
  apply State.Inv1.property <;> assumption

end RelabelNat

def relabelNat (aig : AIG α) : AIG Nat :=
  let map := RelabelNat.State.ofAIG aig
  aig.relabel fun x =>
    -- The none branch never gets hit, we prove this below
    match map.find? x with
    | some var => var
    | none => 0

@[simp]
theorem relabelNat_size_eq_size {aig : AIG α} : aig.relabelNat.decls.size = aig.decls.size := by
  simp [relabelNat]

theorem relabelNat_unsat_iff [Nonempty α] {aig : AIG α} {hidx1} {hidx2}
    : (aig.relabelNat).unsatAt idx hidx1 ↔ aig.unsatAt idx hidx2 := by
  dsimp [relabelNat]
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

def relabelNat (entry : Entrypoint α) : Entrypoint Nat :=
  { entry with
      aig := entry.aig.relabelNat
      inv := by simp[entry.inv]
  }

theorem relabelNat_unsat_iff {entry : Entrypoint α} [Nonempty α]
    : (entry.relabelNat).unsat ↔ entry.unsat:= by
  simp [relabelNat, unsat]
  rw [AIG.relabelNat_unsat_iff]

end Entrypoint
end AIG

