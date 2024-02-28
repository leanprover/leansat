/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Data.HashMap
import LeanSAT.Reflect.Tactics.Attr
import LeanSAT.Reflect.BoolExpr.Nat

set_option linter.missingDocs false

open Lean Meta BoolExprNat

namespace ReflectSat

/-- The internal state for the `ReflectSat.M` monad, recording previously encountered atoms. -/
structure State where
  /-- The atoms up-to-defeq encountered so far. -/
  atoms : HashMap Expr Nat := {}
  stashedAtomsFn? : Option Expr := none

/-- The `ReflectSat.M` monad. -/
abbrev M := StateRefT State MetaM

namespace M

instance : Inhabited (M α) := ⟨failure⟩

/-- Run a computation in the `ReflectSat.M` monad, starting with no recorded atoms. -/
def run (m : M α) : MetaM α :=
  m.run' { } { }

/-- Retrieve the atoms. -/
def atoms : M (List Expr) :=
  return (← getThe State).atoms.toArray.qsort (·.2 < ·.2) |>.map (·.1) |>.toList

/-- Return the `Expr` representing the list of atoms. -/
def atomsList : M Expr := do mkListLit (.const ``Bool []) (← atoms)

/-- Returns the expression `fun i => atomsList.getD i false`. -/
def atomsFn : M Expr := do
  return .lam `i (.const ``Nat []) (mkApp4 (.const ``List.getD [0]) (.const ``Bool [])
    (← atomsList) (.bvar 0) (.const ``false [])) .default

def stashedAtomsFn : M Expr := do
  match (← get).stashedAtomsFn? with
  | none =>
    let r ← atomsFn
    set { (← get) with stashedAtomsFn? := r }
    return r
  | some r => return r

/--
Look up an expression in the atoms, recording it if it has not previously appeared.
-/
-- TODO use a hash map here, and don't use `isDefEq`.
def lookup (e : Expr) : M Nat := do
  let c ← getThe State
  match c.atoms.find? e with
  | some i => return i
  | none =>
  trace[sat] "New atom: {e}"
  let i ← modifyGetThe State
    fun c => (c.atoms.size, { c with atoms := c.atoms.insert e c.atoms.size })
  return i

end M

instance : ToExpr Gate where
  toExpr
  | .and => .const ``Gate.and []
  | .or  => .const ``Gate.or  []
  | .xor => .const ``Gate.xor []
  | .beq => .const ``Gate.beq []
  | .imp => .const ``Gate.imp []
  toTypeExpr := .const ``Gate []

def literalExpr (i : Nat) : Expr := .app (.const ``BoolExprNat.literal []) (mkRawNatLit i)
def constExpr (b : Bool) : Expr := .app (.const ``BoolExprNat.const []) (toExpr b)
def notExpr (x : Expr) : Expr := .app (.const ``BoolExprNat.not []) x
def gateExpr (g : Gate) (x y : Expr) : Expr :=
  mkApp3 (.const ``BoolExprNat.gate []) (toExpr g) x y

instance : ToExpr BoolExprNat where
  toExpr x := t x
  toTypeExpr := .const ``BoolExprNat []
where
  t : BoolExprNat → Expr
  | .literal i => literalExpr i
  | .const b => constExpr b
  | .not x => notExpr (t x)
  | .gate g x y => gateExpr g (t x) (t y)

def mkEvalExpr (x : Expr) (atomsFn : Expr) :
  Expr := mkApp2 (.const ``BoolExprNat.eval []) atomsFn x

structure EvalAtAtoms where
  boolExpr : BoolExprNat
  expr : Expr -- `toExpr boolExpr`
  eval : M (Option Expr) -- a proof that `boolExpr.eval atomsFn = _`, or none for a `rfl` proof.

namespace EvalAtAtoms

def mkAtom (e : Expr) : M EvalAtAtoms := do
  let i ← M.lookup e
  return ⟨.literal i, literalExpr i, pure none⟩

theorem not_congr {x₁ x₂ : Bool} (h : x₁ = x₂) : (!x₁) = (!x₂) := by
  cases h; rfl

theorem and_congr {x₁ x₂ y₁ y₂ : Bool} (hx : x₁ = x₂) (hy : y₁ = y₂) : (x₁ && y₁) = (x₂ && y₂) := by
  cases hx; cases hy; rfl
theorem and_congr_left {x₁ x₂ y : Bool} (hx : x₁ = x₂) : (x₁ && y) = (x₂ && y) := by
  cases hx; rfl
theorem and_congr_right {x y₁ y₂ : Bool} (hy : y₁ = y₂) : (x && y₁) = (x && y₂) := by
  cases hy; rfl

theorem or_congr {x₁ x₂ y₁ y₂ : Bool} (hx : x₁ = x₂) (hy : y₁ = y₂) : (x₁ || y₁) = (x₂ || y₂) := by
  cases hx; cases hy; rfl
theorem or_congr_left {x₁ x₂ y : Bool} (hx : x₁ = x₂) : (x₁ || y) = (x₂ || y) := by
  cases hx; rfl
theorem or_congr_right {x y₁ y₂ : Bool} (hy : y₁ = y₂) : (x || y₁) = (x || y₂) := by
  cases hy; rfl

theorem xor_congr {x₁ x₂ y₁ y₂ : Bool} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Bool.xor x₁ y₁) = (Bool.xor x₂ y₂) := by
  cases hx; cases hy; rfl
theorem xor_congr_left {x₁ x₂ y : Bool} (hx : x₁ = x₂) : (Bool.xor x₁ y) = (Bool.xor x₂ y) := by
  cases hx; rfl
theorem xor_congr_right {x y₁ y₂ : Bool} (hy : y₁ = y₂) : (Bool.xor x y₁) = (Bool.xor x y₂) := by
  cases hy; rfl

theorem beq_congr {x₁ x₂ y₁ y₂ : Bool} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (x₁ == y₁) = (x₂ == y₂) := by
  cases hx; cases hy; rfl
theorem beq_congr_left {x₁ x₂ y : Bool} (hx : x₁ = x₂) : (x₁ == y) = (x₂ == y) := by
  cases hx; rfl
theorem beq_congr_right {x y₁ y₂ : Bool} (hy : y₁ = y₂) : (x == y₁) = (x == y₂) := by
  cases hy; rfl

theorem imp_congr {x₁ x₂ y₁ y₂ : Bool} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (!x₁ ∨ y₁) = (!x₂ ∨ y₂) := by
  cases hx; cases hy; rfl
theorem imp_congr_left {x₁ x₂ y : Bool} (hx : x₁ = x₂) : (!x₁ ∨ y) = (!x₂ ∨ y) := by
  cases hx; rfl
theorem imp_congr_right {x y₁ y₂ : Bool} (hy : y₁ = y₂) : (!x ∨ y₁) = (!x ∨ y₂) := by
  cases hy; rfl

def mkGateCongr (g : Gate) (x y xe ye : Expr) (xp yp : M (Option Expr)) : M (Option Expr) := do
  match (← xp), (← yp) with
  | none, none => return none
  | some xp, none => do
    let n := match g with
    | .and => ``and_congr_left
    | .or =>  ``or_congr_left
    | .xor => ``xor_congr_left
    | .beq => ``beq_congr_left
    | .imp => ``imp_congr_left
    return some <| mkApp4 (.const n []) (mkEvalExpr xe (← M.stashedAtomsFn)) x y xp
  | none, some yp => do
    let n := match g with
    | .and => ``and_congr_right
    | .or =>  ``or_congr_right
    | .xor => ``xor_congr_right
    | .beq => ``beq_congr_right
    | .imp => ``imp_congr_right
    return some <| mkApp4 (.const n []) x (mkEvalExpr ye (← M.stashedAtomsFn)) y yp
  | some xp, some yp => do
    let atomsFn ← M.stashedAtomsFn
    let n := match g with
    | .and => ``and_congr
    | .or =>  ``or_congr
    | .xor => ``xor_congr
    | .beq => ``beq_congr
    | .imp => ``imp_congr
    return some <| mkApp6 (.const n [])
          (mkEvalExpr xe atomsFn) x (mkEvalExpr ye atomsFn) y xp yp

partial def of (e : Expr) : M EvalAtAtoms := do
  match e with
  | .const ``true [] => return ⟨.const true, constExpr true, pure none⟩
  | .const ``false [] => return ⟨.const false, constExpr false, pure none⟩
  | .app _ _ => match e.getAppFnArgs with
    | (``_root_.not, #[x]) => do
      let ⟨xb, xe, xp⟩ ← of x
      let p := do
        match (← xp) with
        | none => pure none
        | some xp => pure (some (mkApp3 (.const ``not_congr []) (mkEvalExpr xe (← M.stashedAtomsFn)) x xp))
      return ⟨.not xb, notExpr xe, p⟩
    | (n, #[x, y]) => do
      let g? : Option Gate := match n with
      | ``_root_.and => some .and
      | ``_root_.or => some .or
      | ``Bool.xor => some .xor
      | ``BEq.beq => some .beq
      | _ => none
      let some g := g? | mkAtom e
      let ⟨xb, xe, xp⟩ ← of x
      let ⟨yb, ye, yp⟩ ← of y
      let p := mkGateCongr g x y xe ye xp yp
      return ⟨.gate g xb yb, gateExpr g xe ye, p⟩
    | _ => mkAtom e
  | _ => mkAtom e

end EvalAtAtoms

structure SatAtAtoms where
  boolExpr : BoolExprNat
  expr : Expr -- `toExpr boolExpr`, cached
  satAtAtoms : M Expr -- a proof that `expr.eval atomsFn = true`

namespace SatAtAtoms

def trivial : SatAtAtoms where
  boolExpr := .const true
  expr := toExpr (.const true : BoolExprNat)
  satAtAtoms := return .app (.const ``sat_true []) (← M.stashedAtomsFn)

def and (x y : SatAtAtoms) : SatAtAtoms where
  boolExpr := .gate .and x.boolExpr y.boolExpr
  expr := gateExpr .and x.expr y.expr
  satAtAtoms := do
    pure <|
    (mkApp5 (.const ``BoolExprNat.sat_and [])
      x.expr y.expr (← M.stashedAtomsFn) (← x.satAtAtoms) (← y.satAtAtoms))

theorem false_of_eq_true_of_eq_false (h₁ : x = true) (h₂ : x = false) : False := by
  cases h₁; cases h₂

/-- Given a proof that `x.expr.unsat`, produce a proof of `False`. -/
def proveFalse (x : SatAtAtoms) (h : Expr) : M Expr := do
  let atomsFn ← M.stashedAtomsFn
  return mkApp3 (.const ``false_of_eq_true_of_eq_false [])
    (mkEvalExpr x.expr atomsFn) (← x.satAtAtoms) (.app h atomsFn)

theorem beq_eq_true_of_eq {x y : Bool} (h : x = y) : (x == y) = true := (beq_iff_eq x y).mpr h

theorem eq_not_of_ne {x y : Bool} (h : x ≠ y) : x = !y := by
  revert h
  cases x <;> cases y <;> simp

def mkSymm (x y : Expr) : Option Expr → Option Expr
  | none => none
  | some e => some <| mkApp4 (.const ``Eq.symm [1]) (.const ``Bool []) x y e

def mkTrans (x y z : Expr) : Option Expr → Option Expr → Option Expr
  | none, none => none
  | some e, none => some e
  | none, some e => some e
  | some e₁, some e₂ => some <| mkApp6 (.const ``Eq.trans [1]) (.const ``Bool []) x y z e₁ e₂

partial def of (h : Expr) : M (Option SatAtAtoms) := do
  let t ← instantiateMVars (← whnfR (← inferType h))
  match t.getAppFnArgs with
  -- We could special case `x` or `y` being true or false.
  | (``Eq, #[.const ``Bool [], x, y]) =>
    let ⟨xb, xe, xp⟩ ← EvalAtAtoms.of x
    let ⟨yb, ye, yp⟩ ← EvalAtAtoms.of y
    let p := do
       let atomsFn ← M.stashedAtomsFn
       let xeval := mkEvalExpr xe atomsFn
       let yeval := mkEvalExpr ye atomsFn
       return mkApp3 (.const ``beq_eq_true_of_eq [])
         xeval yeval
         ((mkTrans xeval y yeval
           (mkTrans xeval x y (← xp) (some h))
           (mkSymm yeval y (← yp))).getD (mkApp2 (.const ``Eq.refl [1]) (.const ``Bool []) xeval))
    return some ⟨.gate .beq xb yb, gateExpr .beq xe ye, p⟩
  | (``Ne, #[_, x, y]) => of (mkApp3 (.const ``eq_not_of_ne []) x y h)
  | (``Not, #[w]) =>
    match w.getAppFnArgs with
    | (``Eq, #[.const ``Bool [], x, y]) => of (mkApp3 (.const ``eq_not_of_ne []) x y h)
    | _ => return none
  | _ => return none

end SatAtAtoms

/--
Given a goal `g`, which should be `False`, returns
* a `e : BoolExprNat` (representing the conjunction of all boolean expressions in hypotheses of `g`)
* a function which takes an expression representing a proof of `e.unsat`,
  and returns a proof of `False` valid in the context of `g`.
-/
def reflectSAT (g : MVarId) : M (BoolExprNat × (Expr → M Expr)) := g.withContext do
  let hyps ← getLocalHyps
  let sats ← hyps.filterMapM fun h => SatAtAtoms.of h
  let sat := sats.foldl (init := SatAtAtoms.trivial) SatAtAtoms.and
  return (sat.boolExpr, sat.proveFalse)
