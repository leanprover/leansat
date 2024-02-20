/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.CNF.Basic

set_option linter.missingDocs false

namespace CNF

namespace Clause

def relabel (f : α → β) (c : Clause α) : Clause β := c.map (fun (i, n) => (f i, n))

def maxLiteral (c : Clause Nat) : Option Nat := (c.map (·.1)) |>.minimum?

end Clause

/-! ### Relabelling

It is convenient to be able to construct a CNF using a more complicated literal type,
but eventually we need to embed in Nat.
-/

def relabel (f : α → β) (g : CNF α) : CNF β := g.map (Clause.relabel f)

theorem sat_relabel (h : sat g (k ∘ f)) : sat (relabel k g) f := sorry
theorem unsat_relabel (h : unsat g) : unsat (relabel k g) := sorry
theorem unsat_relabel_iff (w : ∀ a b, k a = k b → a = b) : unsat (relabel k g) ↔ unsat g := sorry

end CNF
