/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Data.HashMap
import LeanSAT.Reflect.Tactics.Attr
import LeanSAT.Reflect.BoolExpr.Basic

set_option linter.missingDocs false

open Lean Meta BoolExpr

namespace ReflectSat

/-- The internal state for the `ReflectSat.M` monad, recording previously encountered atoms. -/
structure State where
  /-- The atoms up-to-defeq encountered so far. -/
  atoms : Array Expr := #[]

/-- The `ReflectSat.M` monad. -/
abbrev M := StateRefT State MetaM

namespace M

instance : Inhabited (M α) := ⟨failure⟩

/-- Run a computation in the `ReflectSat.M` monad, starting with no recorded atoms. -/
def run (m : M α) : MetaM α :=
  m.run' { } { }

/-- Retrieve the atoms. -/
def atoms : M (List Expr) := return (← getThe State).atoms.toList

/-- Return the `Expr` representing the list of atoms. -/
def atomsList : M Expr := do mkListLit (.const ``Bool []) (← atoms)

/-- Returns the expression `fun i => atomsList.getD i false`. -/
def atomsFn : M Expr := do
  return .lam `i (.const ``Nat []) (mkApp4 (.const ``List.getD [0]) (.const ``Bool [])
    (← atomsList) (.bvar 0) (.const ``false [])) .default

/--
Look up an expression in the atoms, recording it if it has not previously appeared.
-/
def lookup (e : Expr) : M Nat := do
  let c ← getThe State
  for h : i in [:c.atoms.size] do
    if ← isDefEq e c.atoms[i] then
      return i
  trace[sat] "New atom: {e}"
  let i ← modifyGetThe State fun c => (c.atoms.size, { c with atoms := c.atoms.push e })
  return i

end M

structure EvalAtAtoms where
  boolExpr : BoolExpr Nat
  eval : M Expr -- a proof that `boolExpr.eval atomsFn = _`

namespace EvalAtAtoms

def mkAtom (e : Expr) : M EvalAtAtoms := return ⟨.literal (← M.lookup e), do mkEqRefl e⟩

theorem not_congr {x₁ x₂ : Bool} (h : x₁ = x₂) : (!x₁) = (!x₂) := by
  cases h; rfl

theorem and_congr {x₁ x₂ y₁ y₂ : Bool} (hx : x₁ = x₂) (hy : y₁ = y₂) : (x₁ && y₁) = (x₂ && y₂) := by
  cases hx; cases hy; rfl

theorem or_congr {x₁ x₂ y₁ y₂ : Bool} (hx : x₁ = x₂) (hy : y₁ = y₂) : (x₁ || y₁) = (x₂ || y₂) := by
  cases hx; cases hy; rfl

theorem xor_congr {x₁ x₂ y₁ y₂ : Bool} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Bool.xor x₁ y₁) = (Bool.xor x₂ y₂) := by
  cases hx; cases hy; rfl

theorem beq_congr {x₁ x₂ y₁ y₂ : Bool} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (x₁ == y₁) = (x₂ == y₂) := by
  cases hx; cases hy; rfl

partial def of (e : Expr) : M EvalAtAtoms := do
  match e with
  | .const ``true [] => return ⟨.const true, do mkEqRefl e⟩
  | .const ``false [] => return ⟨.const false, do mkEqRefl e⟩
  | .app _ _ => match e.getAppFnArgs with
    | (``_root_.not, #[x]) => do
      let ⟨xb, xp⟩ ← of x
      let p := do mkAppM ``not_congr #[(← xp)]
      return ⟨.not xb, p⟩
    | (``_root_.and, #[x, y]) => do
      let ⟨xb, xp⟩ ← of x
      let ⟨yb, yp⟩ ← of y
      let p := do mkAppM ``and_congr #[(← xp), (← yp)]
      return ⟨.gate .and xb yb, p⟩
    | (``_root_.or, #[x, y]) => do
      let ⟨xb, xp⟩ ← of x
      let ⟨yb, yp⟩ ← of y
      let p := do mkAppM ``or_congr #[(← xp), (← yp)]
      return ⟨.gate .or xb yb, p⟩
    | (``Bool.xor, #[x, y]) => do
      let ⟨xb, xp⟩ ← of x
      let ⟨yb, yp⟩ ← of y
      let p := do mkAppM ``xor_congr #[(← xp), (← yp)]
      return ⟨.gate .xor xb yb, p⟩
    | (``BEq.beq, #[_, _, x, y]) => do
      let ⟨xb, xp⟩ ← of x
      let ⟨yb, yp⟩ ← of y
      let p := do mkAppM ``beq_congr #[(← xp), (← yp)]
      return ⟨.gate .beq xb yb, p⟩
    | _ => mkAtom e
  | _ => mkAtom e

end EvalAtAtoms

instance : ToExpr Gate where
  toExpr
  | .and => .const ``Gate.and []
  | .or  => .const ``Gate.or  []
  | .xor => .const ``Gate.xor []
  | .beq => .const ``Gate.beq []
  | .imp => .const ``Gate.imp []
  toTypeExpr := .const ``Gate []

instance : ToExpr (BoolExpr Nat) where
  toExpr x := t x
  toTypeExpr := .app (.const ``BoolExpr []) (.const ``Nat [])
where
  t : BoolExpr Nat → Expr
  | .literal i => mkApp2 (.const ``BoolExpr.literal []) (.const ``Nat []) (toExpr i)
  | .const b => mkApp2 (.const ``BoolExpr.const []) (.const ``Nat []) (toExpr b)
  | .not x => mkApp2 (.const ``BoolExpr.not []) (.const ``Nat []) (t x)
  | .gate g x y => mkApp4 (.const ``BoolExpr.gate []) (.const ``Nat []) (toExpr g) (t x) (t y)

structure SatAtAtoms where
  expr : BoolExpr Nat
  satAtAtoms : M Expr -- a proof that `expr.eval atomsFn = true`

namespace SatAtAtoms

def trivial : SatAtAtoms where
  expr := .const true
  satAtAtoms := return mkApp2 (.const ``sat_true []) (.const ``Nat []) (← M.atomsFn)

def and (x y : SatAtAtoms) : SatAtAtoms where
  expr := .gate .and x.expr y.expr
  satAtAtoms := do
    pure <|
    (mkApp6 (.const ``sat_and []) (.const ``Nat [])
      (toExpr x.expr) (toExpr y.expr) (← M.atomsFn) (← x.satAtAtoms) (← y.satAtAtoms))

theorem false_of_eq_true_of_eq_false (h₁ : x = true) (h₂ : x = false) : False := by
  cases h₁; cases h₂

/-- Given a proof that `x.expr.unsat`, produce a proof of `False`. -/
def false (x : SatAtAtoms) (h : Expr) : M Expr := do
  mkAppM ``false_of_eq_true_of_eq_false #[← x.satAtAtoms, .app h (← M.atomsFn)]

theorem beq_eq_true_of_eq {x y : Bool} (h : x = y) : (x == y) = true := (beq_iff_eq x y).mpr h

theorem eq_not_of_ne {x y : Bool} (h : x ≠ y) : x = !y := by
  revert h
  cases x <;> cases y <;> simp

partial def of (h : Expr) : M (Option SatAtAtoms) := do
  let t ← instantiateMVars (← whnfR (← inferType h))
  match t.getAppFnArgs with
  -- We could special case `x` or `y` being true or false.
  | (``Eq, #[.const ``Bool [], x, y]) =>
    let ⟨xb, xp⟩ ← EvalAtAtoms.of x
    let ⟨yb, yp⟩ ← EvalAtAtoms.of y
    let p := do
       mkAppM ``beq_eq_true_of_eq #[← mkEqTrans (← mkEqTrans (← xp) h) (← mkEqSymm (← yp))]
    return some ⟨.gate .beq xb yb, p⟩
  | (``Ne, #[_, x, y]) => of (mkApp3 (.const ``eq_not_of_ne []) x y h)
  | (``Not, #[w]) =>
    match w.getAppFnArgs with
    | (``Eq, #[.const ``Bool [], x, y]) => of (mkApp3 (.const ``eq_not_of_ne []) x y h)
    | _ => return none
  | _ => return none

end SatAtAtoms

/--
Given a goal `g`, which should be `False`, returns
* a `e : BoolExpr Nat` (representing the conjunction of all boolean expressions in hypotheses of `g`)
* a function which takes an expression representing a proof of `e.unsat`,
  and returns a proof of `False` valid in the context of `g`.
-/
def reflectSAT (g : MVarId) : M (BoolExpr Nat × (Expr → M Expr)) := g.withContext do
  let hyps ← getLocalHyps
  let sats ← hyps.filterMapM fun h => SatAtAtoms.of h
  let sat := sats.foldl (init := SatAtAtoms.trivial) SatAtAtoms.and
  return (sat.expr, sat.false)
