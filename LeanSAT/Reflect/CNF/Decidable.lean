/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.CNF.Relabel
import LeanSAT.Reflect.Fin

set_option linter.missingDocs false

/-! ### Decidability

(Lower-priority)

It is nice for testing purposes to have a decidability instance (i.e. case bashing).
For that we need to relabel in `Fin k` for some `k`.
-/

namespace CNF

def Clause.maxLiteral (c : Clause Nat) : Option Nat := (c.map (·.1)) |>.minimum?

def maxLiteral (g : CNF Nat) : Option Nat :=
  g.foldl (init := none) fun
    | none, c => c.maxLiteral
    | some m, c => match c.maxLiteral with
      | some m' => some (max m m')
      | none => m

def numLiterals (g : CNF Nat) :=
  match g.maxLiteral with
  | none => 0
  | some n => n + 1

theorem lt_numLiterals {g : CNF Nat} (h : mem a g) : a < numLiterals g := sorry

theorem numLiterals_pos {g : CNF Nat} (h : mem a g) : 0 < numLiterals g :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (lt_numLiterals h)

def relabelFin (g : CNF Nat) : CNF (Fin g.numLiterals) :=
  if h : ∃ a, mem a g then
    let n := g.numLiterals
    g.relabel fun i =>
      if w : i < n then
        -- This branch will always hold
        ⟨i, w⟩
      else
        ⟨0, numLiterals_pos h.choose_spec⟩
  else
    []

theorem unsat_relabelFin : unsat g.relabelFin ↔ unsat g := by
  dsimp [relabelFin]
  split <;> rename_i h
  · apply unsat_relabel_iff
    intro a b ma mb
    replace ma := lt_numLiterals ma
    replace mb := lt_numLiterals mb
    split <;> rename_i a_lt
    · simp
    · contradiction
  · sorry

instance (x : CNF (Fin n)) : Decidable x.unsat :=
  inferInstanceAs <| Decidable (∀ f, eval f x = false)

instance (x : CNF Nat) : Decidable x.unsat :=
  decidable_of_iff _ unsat_relabelFin

end CNF
