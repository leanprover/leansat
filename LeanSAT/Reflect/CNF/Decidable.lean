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

def relabelFin (g : CNF Nat) : CNF (Fin g.numLiterals) := g.relabel fun i => ⟨i, sorry⟩

theorem unsat_relabelFin : unsat g.relabelFin ↔ unsat g := sorry

instance (x : CNF (Fin n)) : Decidable x.unsat :=
  inferInstanceAs <| Decidable (∀ f, eval f x = false)

instance (x : CNF Nat) : Decidable x.unsat :=
  decidable_of_iff _ unsat_relabelFin

end CNF
