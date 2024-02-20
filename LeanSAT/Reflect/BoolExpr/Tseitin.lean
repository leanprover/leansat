/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.BoolExpr.Decidable
import LeanSAT.Reflect.CNF.Relabel
import LeanSAT.Reflect.CNF.Decidable
import Std.Tactic.LibrarySearch

@[simp] theorem false_beq_false : (false == false) = true := rfl
@[simp] theorem false_beq_true : (false == true) = false := rfl
@[simp] theorem true_beq_false : (true == false) = false := rfl
@[simp] theorem true_beq_true : (true == true) = true := rfl

namespace Gate

def toCNF (i₁ i₂ o : α) : Gate → CNF α
  | .and =>
    [[(o, true), (i₁, false)], [(o, true), (i₂, false)], [(o, false), (i₁, true), (i₂, true)]]
  | .or =>
    [[(o, false), (i₁, true)], [(o, false), (i₂, true)], [(o, true), (i₁, false), (i₂, false)]]
  | .xor =>
    [[(o, true), (i₁, false), (i₂, false)], [(o, true), (i₁, true), (i₂, true)],
      [(o, false), (i₁, true), (i₂, false)], [(o, false), (i₁, false), (i₂, true)]]
  | .beq =>
    [[(o, true), (i₁, false), (i₂, true)], [(o, true), (i₁, true), (i₂, false)],
      [(o, false), (i₁, true), (i₂, true)], [(o, false), (i₁, false), (i₂, false)]]
  | .imp =>
    [[(o, true), (i₁, true), (i₂, false)], [(o, false), (i₁, false)], [(o, false), (i₂, true)]]

theorem toCNF_sat : (toCNF i₁ i₂ o g).sat f ↔ f o = g.eval (f i₁) (f i₂) := by
  match g with
  | .and
  | .or
  | .xor
  | .beq
  | .imp =>
    simp [toCNF, eval, CNF.sat, CNF.eval, CNF.Clause.eval]
    cases f o <;> cases f i₁ <;> cases f i₂ <;> simp

end Gate

namespace CNF

def eq (x y : α) : CNF α := [[(x, true), (y, false)], [(x, false), (y, true)]]

theorem eq_sat : (eq x y).sat f ↔ f x = f y := by
  simp [eq, eval, CNF.sat, CNF.eval, CNF.Clause.eval]
  cases f x <;> cases f y <;> simp

def ne (x y : α) : CNF α := [[(x, true), (y, true)], [(x, false), (y, false)]]

theorem ne_sat : (ne x y).sat f ↔ f x = !f y := by
  simp [ne, eval, CNF.sat, CNF.eval, CNF.Clause.eval]
  cases f x <;> cases f y <;> simp
end CNF

namespace BoolExpr

/-!
This is work in progress, and seems nontrivial.
We need `def toCNF : BoolExpr Nat → CNF Nat`,
and `theorem toCNF_unsat : (toCNF x).unsat ↔ x.unsat`.
I don't mind whether it follows the approach below (which may well be buggy!) or not.

It seems we need to attach information to the nodes of a `BoolExpr` in multiple ways:
* Numbering the nodes (so they can be CNF literals)
* The CNF clauses expressing the relation between inputs and outputs (in terms of those numbers)
* The `Bool` at each node as we propagate the evaluation of an input.
* The fact that these propagated `Bool`s satisfy the CNF clauses.

This suggests we should construct all four of these things in a uniform manner,
but I don't see how to set this up yet.
-/

/-
Implementation of `BoolExpr.toCNF`.

We produce a CNF with literals labelled by `α ⊕ Nat`.
- `.inl a` represents an "input node" corresponding to a literal in the original `BoolExpr`
- `.inr j` represents a "circuit node" corresponding to
  a gate (0-ary, 1-ary, or 2-ary) in the `BoolExpr`.
-/
def toCNF' (x : BoolExpr α) : CNF (α ⊕ Nat) :=
  let (_, c, p) := run 0 x
  [(p, false)] :: c
where
  /--
  We take as additional argument `k : Nat` which is the "next available circuit node label"
  and return an `α ⊕ Nat`, the label of the "output node".
  -/
  run (k : Nat) : BoolExpr α → Nat × CNF (α ⊕ Nat) × (α ⊕ Nat)
  | .literal a => (k + 1, CNF.eq (.inl a) (.inr k), .inr k)
  | .const b => (k + 1, [[(.inr k, !b)]], .inr k)
  | .not x => match run k x with
    | (k', c, p) => (k' + 1, CNF.ne (.inr k') p ++ c, .inr k')
  | .gate g x y => match run k x with
    | (kx, cx, px) => match run kx y with
      | (ky, cy, py) =>
        (ky + 1, g.toCNF px py (.inr ky) ++ cx ++ cy, .inr ky)

theorem toCNF'_run_eval (k : Nat) (x : BoolExpr α) :
    let (_, c, p) := toCNF'.run k x
    c.eval f = (x.eval (fun a => f (.inl a)) == f p) :=
  sorry

theorem toCNF'_eval {x : BoolExpr α} : (toCNF' x).eval f = x.eval (fun a => f (.inl a)) :=
  sorry

-- the output of the `k`-th gate
def traceEval (x : BoolExpr α) (f : α → Bool) (k : Nat) : Bool := sorry

theorem toCNF'_eval_elim_traceEval {x : BoolExpr α} (f : α → Bool) :
    (toCNF' x).eval (Sum.elim f (x.traceEval f)) = x.eval f :=
  sorry

theorem toCNF'_unsat {x : BoolExpr α} : (toCNF' x).unsat ↔ x.unsat := by
  constructor
  · intro h f
    specialize h (Sum.elim f (traceEval x f))
    rwa [toCNF'_eval_elim_traceEval] at h
  · intro h f
    specialize h (fun a => f (.inl a))
    rwa [toCNF'_eval]

def toCNF (x : BoolExpr Nat) : CNF Nat :=
  (toCNF' x.attach).relabel fun | .inl a => a | .inr j => x.vars + j

theorem toCNF_unsat : (toCNF x).unsat ↔ x.unsat := by
  dsimp [toCNF]
  rw [CNF.unsat_relabel_iff, toCNF'_unsat, ← BoolExpr.attach_unsat]
  · rintro (a | a) (b | b) <;> simp
    exact Fin.eq_of_val_eq -- FIXME `omega` should handle this too!
    all_goals omega

theorem unsat_of_toCNF_unsat (h : (toCNF x).unsat) : x.unsat := toCNF_unsat.mp h

end BoolExpr
