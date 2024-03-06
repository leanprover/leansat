/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.Reflect.Tactics.SatDecide

open Lean Meta

namespace BVDecide

-- TODO: This should be upstream?
instance : ToExpr (BitVec w) where
  toExpr bv := mkApp2 (mkConst ``BitVec.ofNat) (toExpr w) (toExpr bv.toNat)
  toTypeExpr := mkApp (mkConst ``BitVec) (toExpr w)

instance : ToExpr BVBinPred where
  toExpr x :=
    match x with
    | .eq => mkConst ``BVBinPred.eq
  toTypeExpr := mkConst ``BVBinPred

instance : ToExpr BVUnOp where
  toExpr x :=
    match x with
    | .not => mkConst ``BVUnOp.not
  toTypeExpr := mkConst ``BVUnOp

instance : ToExpr BVBinOp where
  toExpr x :=
    match x with
    | .and => mkConst ``BVBinOp.and
  toTypeExpr := mkConst ``BVBinOp

instance : ToExpr (BVExpr w) where
  toExpr x := go x
  toTypeExpr := mkApp (mkConst ``BVExpr) (toExpr w)
where
  go : BVExpr w → Expr
| .var idx => mkApp2 (mkConst ``BVExpr.var) (toExpr w) (toExpr idx)
| .const val => mkApp2 (mkConst ``BVExpr.const) (toExpr w) (toExpr val)
| .bin lhs op rhs => mkApp4 (mkConst ``BVExpr.bin) (toExpr w) (go lhs) (toExpr op) (go rhs)
| .un op operand => mkApp3 (mkConst ``BVExpr.un) (toExpr w) (toExpr op) (go operand)

instance : ToExpr BVPred where
  toExpr x := go x
  toTypeExpr := mkConst ``BVPred
where
  go : BVPred → Expr
  | .bin (w := w) lhs op rhs => mkApp4 (mkConst ``BVPred.bin) (toExpr w) (toExpr lhs) (toExpr op) (toExpr rhs)

instance : ToExpr BVLogicalExpr where
  toExpr x := go x
  toTypeExpr := mkConst ``BVLogicalExpr
where
  go : BVLogicalExpr → Expr
  | .literal pred => mkApp2 (mkConst ``BoolExpr.literal) (toTypeExpr BVPred) (toExpr pred)
  | .const b => mkApp2 (mkConst ``BoolExpr.const) (toTypeExpr BVPred) (toExpr b)
  | .not x => mkApp2 (mkConst ``BoolExpr.not) (toTypeExpr BVPred) (go x)
  | .gate g x y => mkApp4 (mkConst ``BoolExpr.gate) (toTypeExpr BVPred) (toExpr g) (go x) (go y)


structure State where
  /--
  The atoms encountered so far. Saved as a map from `BitVec` expressions to a
  width × atomNumber pair.
  -/
  atoms : HashMap Expr (Nat × Nat) := {}

abbrev M := StateRefT State MetaM

namespace M

def run (m : M α) : MetaM α :=
  m.run' { } { }

/-- Retrieve the atoms. -/
def atoms : M (List (Nat × Expr)) :=
  return (← getThe State).atoms.toArray.qsort (·.2.2 < ·.2.2) |>.map (fun (expr, width, _) => (width, expr)) |>.toList

def atomsAssignment : M Expr := do
  let as ← atoms
  let packed : List Expr := as.map (fun (width, expr) => mkApp2 (mkConst ``BVExpr.PackedBitVec.mk) (toExpr width) expr)
  let packedType := mkConst ``BVExpr.PackedBitVec
  mkListLit packedType packed

-- TODO: we could store `evalFunc` in `HoldsAtAtoms` and maybe even fill it out with typeclass stuff
def mkEvalExpr (evalFunc : Name) (expr : Expr) : M Expr := do
  return mkApp2 (mkConst evalFunc) (← M.atomsAssignment) expr

end M

-- TODO: how to extract nat literals? Is there code for this?
structure BVAtAtoms (w : Nat) where
  bvExpr : BVExpr w
  evalsAtAtoms : M Expr -- a proof that `expr.eval atomsFn = originalBV`
  expr : Expr -- `toExpr bvExpr`, cached

namespace BVAtAtoms

def mkEvalExpr (w : Nat) (expr : Expr) : M Expr := do
  return mkApp3 (mkConst ``BVExpr.eval) (toExpr w) (← M.atomsAssignment) expr

def of (x : Expr) : M (Option (BVAtAtoms w)) := do
  -- TODO: should I do some whnf operation here? I think I should
  match x.getAppFnArgs with
  -- TODO: OfNat.ofNat support
  | (``BitVec.ofNat, #[_, _]) =>
    let some ⟨width, bvVal⟩ ← getBitVecValue? x | return none
    if h:width = w then
      let bvExpr := .const (h ▸ bvVal)
      let expr := mkApp2 (mkConst ``BVExpr.const) (toExpr w) (toExpr bvVal)
      -- Hopefully by rfl?
      let proof := do
        let evalExpr ← mkEvalExpr w expr
        return mkApp2
          (mkConst ``Eq.refl [1])
          (mkApp (mkConst ``BitVec) (toExpr w))
          evalExpr
      return some ⟨bvExpr, proof, expr⟩
    else
      panic! "Attempt to reify ill-typed BitVec literal"
  | _ => return none

end BVAtAtoms

structure HoldsAtAtoms (α : Type) where
  bvExpr : α
  holdsAtAtoms : M Expr -- a proof that `expr.eval atomsFn = true`
  expr : Expr -- `toExpr bvExpr`, cached

namespace HoldsAtAtoms

theorem beq_eq_true_of_eq {x y : BitVec w} (h : x = y) : (x == y) = true := (beq_iff_eq x y).mpr h

theorem foo {le re : BitVec w} (lhs rhs : BVExpr w) (h1 : lhs.eval [] = le) (h2 : rhs.eval [] = re) (h3 : le = re)
    : lhs.eval [] = rhs.eval [] := by
  apply Eq.trans
  exact h1
  apply Eq.trans
  exact h3
  exact h2.symm

#print foo

partial def of (h : Expr) : M (Option (HoldsAtAtoms BVLogicalExpr)) := do
  -- TODO: naive approach, does not handle any boolean structure on top of our problem
  -- this is no issue for most cases but we *must* handle at least negation of preds
  -- for any proof by contradiction where the goal involves a bitvec expression.
  let some pred ← ofPred h | return none
  let bvExpr := .literal pred.bvExpr
  let expr := mkApp2 (mkConst ``BoolExpr.literal) (mkConst ``BVPred) pred.expr
  let proof := do
    let evalLogic ← M.mkEvalExpr ``BVLogicalExpr.eval expr
    let evalPred ← M.mkEvalExpr ``BVPred.eval pred.expr
    let helper := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) evalLogic
    return mkApp6 (mkConst ``Eq.trans [1])
      (mkConst ``Bool)
      evalLogic
      evalPred
      (mkConst ``Bool.true)
      helper
      (← pred.holdsAtAtoms)
  return some ⟨bvExpr, proof, expr⟩
where
  ofPred (h : Expr) : M (Option (HoldsAtAtoms BVPred)) := do
    let t ← instantiateMVars (← whnfR (← inferType h))
    match t.getAppFnArgs with
    | (``Eq, #[.app (.const ``BitVec []) widthExpr, lhsExpr, rhsExpr]) =>
      let some width ← getNatValue? widthExpr | return none
      let some lhs ← BVAtAtoms.of lhsExpr | return none
      let some rhs ← BVAtAtoms.of rhsExpr | return none
      let bvExpr := .bin (w := width) lhs.bvExpr .eq rhs.bvExpr
      let expr := mkApp4 (mkConst ``BVPred.bin) widthExpr lhs.expr (mkConst ``BVBinPred.eq) rhs.expr
      let proof := do
        let lhsEval ← BVAtAtoms.mkEvalExpr width lhs.expr
        let rhsEval ← BVAtAtoms.mkEvalExpr width rhs.expr
        let eqProof := mkApp6 (mkConst ``Eq.trans [1])
          (mkApp (mkConst ``BitVec) (toExpr width))
          lhsEval
          lhsExpr
          rhsEval
          (← lhs.evalsAtAtoms)
          (mkApp6 (mkConst ``Eq.trans [1])
            (mkApp (mkConst ``BitVec) (toExpr width))
            lhsExpr
            rhsExpr
            rhsEval
            h
            (mkApp4 (mkConst ``Eq.symm [1])
              (mkApp (mkConst ``BitVec) (toExpr width))
              rhsEval
              rhsExpr
              (← rhs.evalsAtAtoms)
            )
          )
        return mkApp4
          (mkConst ``beq_eq_true_of_eq)
          (toExpr width)
          lhsEval
          rhsEval
          eqProof
      return some ⟨bvExpr, proof, expr⟩
    | _ => return none

def trivial : HoldsAtAtoms BVLogicalExpr where
  bvExpr := .const true
  expr := toExpr (.const true : BVLogicalExpr)
  holdsAtAtoms := return mkApp (mkConst ``BVLogicalExpr.sat_true) (← M.atomsAssignment)

def and (x y : HoldsAtAtoms BVLogicalExpr) : HoldsAtAtoms BVLogicalExpr where
  bvExpr := .gate .and x.bvExpr y.bvExpr
  expr := mkApp4 (mkConst ``BoolExpr.gate) (mkConst ``BVPred) (mkConst ``Gate.and) x.expr y.expr
  holdsAtAtoms :=
    return mkApp5
      (mkConst ``BVLogicalExpr.sat_and)
      x.expr
      y.expr
      (← M.atomsAssignment)
      (← x.holdsAtAtoms)
      (← y.holdsAtAtoms)

/-- Given a proof that `x.expr.unsat`, produce a proof of `False`. -/
def proveFalse (x : HoldsAtAtoms BVLogicalExpr) (h : Expr) : M Expr := do
  let atomsList ← M.atomsAssignment
  let evalExpr := mkApp2 (mkConst ``BVLogicalExpr.eval) atomsList x.expr
  return mkApp3
    (mkConst ``ReflectSat.SatAtAtoms.false_of_eq_true_of_eq_false)
    evalExpr
    (← x.holdsAtAtoms)
    (.app h atomsList)

end HoldsAtAtoms

/--
Given a goal `g`, which should be `False`, returns
* a `e : BVLogicalExpr` (representing the conjunction of all bitvec predicates in hypotheses of `g`)
* a function which takes an expression representing a proof of `e.unsat`,
  and returns a proof of `False` valid in the context of `g`.
-/
def reflectBV (g : MVarId) : M (BVLogicalExpr × (Expr → M Expr)) := g.withContext do
  let hyps ← getLocalHyps
  let sats ← hyps.filterMapM HoldsAtAtoms.of
  IO.println "reflected things:"
  IO.println <| sats.map (·.bvExpr)
  let sat := sats.foldl (init := HoldsAtAtoms.trivial) HoldsAtAtoms.and
  return (sat.bvExpr, sat.proveFalse)

def _root_.Lean.MVarId.bvDecide (g : MVarId) (cfg : SatDecide.TacticContext) : MetaM Unit := M.run do
  let g' ← falseOrByContra g
  g'.withContext do
    let (bvLogicalExpr, f) ←
      withTraceNode `bv (fun _ => return "Reflecting goal into BVLogicalExpr") do
        reflectBV g'
    trace[bv] "Reflected bv logical expression: {bvLogicalExpr}"
    let aux := mkApp (mkConst ``BVLogicalExpr.unsat) (toExpr bvLogicalExpr)
    let unsatProof := mkApp2 (mkConst ``sorryAx [.zero]) aux (mkConst ``Bool.false)
    let proveFalse ← f unsatProof
    g'.assign proveFalse

syntax (name := bvDecideSyntax) "bv_decide" : tactic

end BVDecide

open Elab.Tactic
elab_rules : tactic
  | `(tactic| bv_decide) => do
    let cfg ← SatDecide.TacticContext.new (← SatDecide.mkTemp)
    liftMetaFinishingTactic fun g => g.bvDecide cfg
