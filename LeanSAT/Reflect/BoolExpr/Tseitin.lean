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

@[simp] theorem false_beq : (false == x) = !x := by cases x <;> simp
@[simp] theorem beq_false : (x == false) = !x := by cases x <;> simp
@[simp] theorem true_beq : (true == x) = x := by cases x <;> simp
@[simp] theorem beq_true : (x == true) = x := by cases x <;> simp

theorem eq_true_or_eq_false {x : Bool} : x = true ∨ x = false := by cases x <;> simp
theorem eq_false_or_eq_true {x : Bool} : x = false ∨ x = true := by cases x <;> simp

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

@[simp] theorem toCNF_eval {i₁ i₂ o : α} : (toCNF i₁ i₂ o g).eval f = (f o == g.eval (f i₁) (f i₂)) := by
  match g with
  | .and
  | .or
  | .xor
  | .beq
  | .imp =>
    simp [toCNF, eval, CNF.eval, CNF.Clause.eval]
    cases f o <;> cases f i₁ <;> cases f i₂ <;> simp

theorem toCNF_sat : (toCNF i₁ i₂ o g).sat f ↔ f o = g.eval (f i₁) (f i₂) := by
  simp [CNF.sat]

end Gate

namespace CNF

def eq (x y : α) : CNF α := [[(x, true), (y, false)], [(x, false), (y, true)]]

@[simp] theorem eq_eval : (eq x y).eval f = (f x == f y) := by
  simp [eq, CNF.eval, CNF.Clause.eval]
  cases f x <;> cases f y <;> simp

theorem eq_sat : (eq x y).sat f ↔ f x = f y := by simp [CNF.sat]

def ne (x y : α) : CNF α := [[(x, true), (y, true)], [(x, false), (y, false)]]

@[simp] theorem ne_eval : (ne x y).eval f = (f x == !f y) := by
  simp [ne, CNF.eval, CNF.Clause.eval]
  cases f x <;> cases f y <;> simp

theorem ne_sat : (ne x y).sat f ↔ f x = !f y := by simp [CNF.sat]

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
  let (c, p) := run 0 x
  [(.inr p, false)] :: c
where
  /--
  We take as additional argument `k : Nat` which is the "next available circuit node label"
  and return an `α ⊕ Nat`, the label of the "output node".
  -/
  run (k : Nat) : BoolExpr α → CNF (α ⊕ Nat) × Nat
  | .literal a => (CNF.eq (.inl a) (.inr k), k)
  | .const b => ([[(.inr k, !b)]], k)
  | .not x => match run k x with
    | (c, nx) => (CNF.ne (.inr (nx + 1)) (.inr nx) ++ c, nx + 1)
  | .gate g x y => match run k x with
    | (cx, nx) => match run (nx + 1) y with
      | (cy, ny) =>
        (g.toCNF (.inr nx) (.inr ny) (.inr (ny + 1)) ++ cx ++ cy, ny + 1)

@[simp] theorem toCNF'_run_snd (x : BoolExpr α) : (toCNF'.run k x).2 = k + x.size - 1 := by
  match x with
  | .literal _
  | .const _
  | .not x
  | .gate _ x y =>
    have := x.size_pos
    simp [toCNF'.run, size, toCNF'_run_snd] <;> omega

theorem toCNF'_run_eval (k : Nat) (x : BoolExpr α) (f : α ⊕ Nat → Bool) :
    let (c, p) := toCNF'.run k x
    !(c.eval f) || (x.eval (fun a => f (.inl a)) == f (.inr p)) := by
  match x with
  | .literal a => simp [toCNF'.run]
  | .const b => simp [toCNF'.run] <;> cases b <;> cases f (Sum.inr k) <;> simp
  | .not x =>
    dsimp only [toCNF'.run]
    have := toCNF'_run_eval k x f
    revert this
    simp
    generalize f (.inr _) = x1
    generalize f (.inr _) = x2
    generalize eval (fun a => f (Sum.inl a)) x = x3
    generalize CNF.eval f (toCNF'.run k x).fst = x4
    cases x1 <;> cases x2 <;> simp
  | .gate g x y =>
    dsimp only [toCNF'.run]
    have := toCNF'_run_eval k x f
    revert this
    have := toCNF'_run_eval ((toCNF'.run k x).2 + 1) y f
    revert this
    simp
    generalize f (.inr _) = x1
    generalize f (.inr _) = x2
    generalize f (.inr _) = x3
    generalize eval (fun a => f (Sum.inl a)) x = x4
    generalize eval (fun a => f (Sum.inl a)) y = x5
    generalize CNF.eval f _ = x6
    generalize CNF.eval f _ = x7
    cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> cases x5 <;> cases x6 <;> cases x7
      <;> simp [eq_true_or_eq_false, eq_false_or_eq_true]

theorem toCNF'_eval (x : BoolExpr α) (f : α ⊕ Nat → Bool) :
    !(toCNF' x).eval f || x.eval (fun a => f (.inl a)) := by
  dsimp [toCNF']
  have := toCNF'_run_eval 0 x f
  revert this
  simp
  generalize f (.inr _) = x1
  generalize eval (fun a => f (Sum.inl a)) x = x2
  cases x1 <;> cases x2 <;> simp

-- the output of the `k`-th gate
def traceEval (x : BoolExpr α) (f : α → Bool) (l : Nat) : Bool :=
  (run 0 x).1
where
  run (k : Nat) : BoolExpr α → Bool × Bool × Nat
  | .literal a => (f a, k = l, k)
  | .const b => (b, k = l, k)
  | .not x => match run k x with
    | (r, d, k') => (bif d then r else !r, d || (k' + 1 = l), k' + 1)
  | .gate g x y => match run k x with
    | (rx, dx, kx) => match run (kx + 1) y with
      | (ry, dy, ky) =>
        (bif dx then rx else bif dy then ry else g.eval rx ry, dx || dy || (ky + 1 = l), ky + 1)

theorem traceEval_run_snd_snd : (traceEval.run f l k x).2.2 = k + x.size - 1 := by
  match x with
  | .literal _ => simp [size, traceEval.run]
  | .const _ => simp [size, traceEval.run]
  | .not x =>
    have := x.size_pos
    simp only [size, traceEval.run] at *
    rw [traceEval_run_snd_snd] <;> omega
  | .gate g x y =>
    have := x.size_pos
    have := y.size_pos
    simp only [size, traceEval.run] at *
    rw [traceEval_run_snd_snd, traceEval_run_snd_snd]
    omega

theorem traceEval_run_snd_fst_of_le (w : k + x.size ≤ l) : (traceEval.run f l k x).2.1 = false := by
  match x with
  | .literal a => simp [size, traceEval.run] at *; omega
  | .const b => simp [size, traceEval.run] at *; omega
  | .not x =>
    have := x.size_pos
    simp only [size, traceEval.run] at *
    rw [traceEval_run_snd_fst_of_le]
    simp only [Bool.false_or, decide_eq_false_iff_not, ne_eq]
    rw [traceEval_run_snd_snd]
    all_goals omega
  | .gate g x y =>
    have := x.size_pos
    have := y.size_pos
    simp only [size, traceEval.run] at *
    rw [traceEval_run_snd_snd, traceEval_run_snd_snd, traceEval_run_snd_fst_of_le,
      traceEval_run_snd_fst_of_le]
    simp only [Bool.or_self, Bool.false_or, decide_eq_false_iff_not, ne_eq]
    all_goals omega

theorem traceEval_run_snd_fst (w₁ : k ≤ l) (w₂ : l < k + x.size) : (traceEval.run f l k x).2.1 = true := by
  match x with
  | .literal a => simp [size, traceEval.run] at *; omega
  | .const b => simp [size, traceEval.run] at *; omega
  | .not x =>
    have := x.size_pos
    simp only [size, traceEval.run] at *
    rw [traceEval_run_snd_snd]
    by_cases w₃ : l < k + x.size
    · rw [traceEval_run_snd_fst]
      simp only [Bool.true_or]
      all_goals omega
    · rw [traceEval_run_snd_fst_of_le]
      simp only [Bool.false_or, decide_eq_true_eq]
      all_goals omega
  | .gate g x y =>
    have := x.size_pos
    have := y.size_pos
    simp only [size, traceEval.run] at *
    rw [traceEval_run_snd_snd, traceEval_run_snd_snd]
    by_cases w₃ : l < k + x.size
    · rw [traceEval_run_snd_fst]
      simp only [Bool.true_or]
      all_goals omega
    · rw [traceEval_run_snd_fst_of_le]
      simp only [Bool.false_or, Bool.or_eq_true, decide_eq_true_eq]
      by_cases w₄ : l < k + x.size + y.size
      · rw [traceEval_run_snd_fst]
        simp only [true_or]
        all_goals omega
      · rw [traceEval_run_snd_fst_of_le]
        simp only [false_or]
        all_goals omega
      omega

theorem traceEval_run_fst (w : k + x.size - 1 ≤ l) : (traceEval.run f l k x).1 = x.eval f := by
  match x with
  | .literal a => simp [size, traceEval.run]
  | .const b => simp [size, traceEval.run]
  | .not x =>
    have := x.size_pos
    simp [size, traceEval.run] at *
    rw [traceEval_run_snd_fst_of_le, traceEval_run_fst]
    simp only [cond_false]
    all_goals omega
  | .gate g x y =>
    have := x.size_pos
    have := y.size_pos
    simp [size, traceEval.run] at *
    rw [traceEval_run_snd_snd, traceEval_run_snd_fst_of_le, traceEval_run_snd_fst_of_le,
      traceEval_run_fst, traceEval_run_fst]
    simp only [cond_false]
    all_goals omega

theorem toCNF'_run_fst_eval_elim_traceEval (x : BoolExpr α) (f : α → Bool) :
    (toCNF'.run 0 x).1.eval (Sum.elim f (x.traceEval f)) = true := by
  match x with
  | .literal a => simp [toCNF'.run, traceEval, traceEval.run]
  | .const b => simp [toCNF'.run, traceEval, traceEval.run]
  | .not x =>
    have := x.size_pos
    have := toCNF'_run_fst_eval_elim_traceEval x f
    revert this
    simp only [toCNF'.run, toCNF'_run_snd, Nat.zero_add, CNF.eval_append, CNF.ne_eval, Sum.elim_inr,
      traceEval, traceEval.run, Nat.succ.injEq, Bool.and_eq_true, beq_iff_eq]
    rw [traceEval_run_snd_fst_of_le, traceEval_run_snd_fst, traceEval_run_fst, traceEval_run_fst]
    have : CNF.eval (Sum.elim f (traceEval (not x) f)) (toCNF'.run 0 x).fst = CNF.eval (Sum.elim f (traceEval x f)) (toCNF'.run 0 x).fst := sorry
    rw [this]
    simp only [cond_false, cond_true, true_and, imp_self]
    all_goals omega
  | .gate g x y => sorry

theorem toCNF'_eval_elim_traceEval (x : BoolExpr α) (f : α → Bool) :
    (toCNF' x).eval (Sum.elim f (x.traceEval f)) = x.eval f := by
  match x with
  | .literal a => simp [toCNF', toCNF'.run, traceEval, traceEval.run]
  | .const b => simp [toCNF', toCNF'.run, traceEval, traceEval.run]
  | .not x =>
    dsimp [toCNF']
    have := toCNF'_run_fst_eval_elim_traceEval x f
    revert this
    simp [toCNF'.run]
    have : CNF.eval (Sum.elim f (traceEval (not x) f)) (toCNF'.run 0 x).fst = CNF.eval (Sum.elim f (traceEval x f)) (toCNF'.run 0 x).fst := sorry
    rw [this]
    generalize CNF.eval (Sum.elim f (traceEval x f)) (toCNF'.run 0 x).fst = x1
    cases x1 <;> simp
    sorry
  | .gate g x y => sorry

theorem toCNF'_unsat {x : BoolExpr α} : (toCNF' x).unsat ↔ x.unsat := by
  constructor
  · intro h f
    specialize h (Sum.elim f (traceEval x f))
    rwa [toCNF'_eval_elim_traceEval] at h
  · intro h f
    specialize h (fun a => f (.inl a))
    revert h
    have := toCNF'_eval x f
    revert this
    cases CNF.eval f (toCNF' x) <;> cases eval (fun a => f (Sum.inl a)) x <;> simp


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
