import LeanSAT.AIG.Relabel

open Std

variable {α : Type} [BEq α] [Hashable α]

namespace AIG

inductive State.Inv1 : Nat → HashMap α Nat → Prop where
| empty : State.Inv1 0 {}
| insert (hinv : State.Inv1 n map) (hfind : map.find? x = none) : State.Inv1 (n + 1) (map.insert x n)

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

structure State (α : Type) [BEq α] [Hashable α] where
  max : Nat
  map : HashMap α Nat
  inv1 : State.Inv1 max map

def State.empty : State α :=
  { max := 0, map := {}, inv1 := State.Inv1.empty }

def State.addVar (state : State α) (x : α) : State α :=
  match h:state.map.find? x with
  | some _ => state
  | none =>
    {
      max := state.max + 1
      map := state.map.insert x state.max
      inv1 := by
        apply State.Inv1.insert
        . exact state.inv1
        . exact h
    }

def State.addDecl (state : State α) (decl : Decl α) : State α :=
  match decl with
  | .atom x => state.addVar x
  | _ => state

def State.ofAIGAux (aig : AIG α) : State α :=
  aig.decls.foldl (init := State.empty) State.addDecl

def State.ofAIG (aig : AIG α) : HashMap α Nat :=
  State.ofAIGAux aig |>.map

theorem State.ofAIG.Inv1 (aig : AIG α) : ∃ n, State.Inv1 n (State.ofAIG aig) := by
  exists (State.ofAIGAux aig).max
  dsimp [ofAIG]
  exact (State.ofAIGAux aig).inv1

/--
This axiom follows because `State.ofAIG` constructs a map that has every atom inserted.
However we cannot prove this yet as we don't have enough HashMap theory
-/
axiom State.ofAIG_find_some {aig : AIG α} : ∀ a ∈ aig, ∃ n, (State.ofAIG aig).find? a = some n


theorem State.ofAIG_find_unique {aig : AIG α} (a : α) (ha : (State.ofAIG aig).find? a = some n)
    : ∀ a', (State.ofAIG aig).find? a' = some n → a = a' := by
  intro a' ha'
  rcases State.ofAIG.Inv1 aig with ⟨n, hn⟩
  apply State.Inv1.property <;> assumption

def relabelNat (aig : AIG α) : AIG Nat :=
  let map := State.ofAIG aig
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
      apply State.ofAIG_find_unique
      . assumption
      . rw [heq]
        assumption
    . next hcase2 =>
      exfalso
      rcases State.ofAIG_find_some y hy with ⟨n, hn⟩
      simp[hcase2] at hn
  . next hcase =>
    exfalso
    rcases State.ofAIG_find_some x hx with ⟨n, hn⟩
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

