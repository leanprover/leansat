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
| .var idx => mkApp (mkConst ``BVExpr.var) (toExpr idx)
| .const val => mkApp (mkConst ``BVExpr.const) (toExpr val)
| .bin lhs op rhs => mkApp3 (mkConst ``BVExpr.bin) (go lhs) (toExpr op) (go rhs)
| .un op operand => mkApp2 (mkConst ``BVExpr.un) (toExpr op) (go operand)

instance : ToExpr BVPred where
  toExpr x := go x
  toTypeExpr := mkConst ``BVPred
where
  go : BVPred → Expr
  | .bin lhs op rhs => mkApp3 (mkConst ``BVPred.bin) (toExpr lhs) (toExpr op) (toExpr rhs)

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

end M

-- TODO: how to extract nat literals? Is there code for this?
def parseNatLit (w : Expr) : Nat := sorry

structure BVAtAtoms (w : Nat) where
  bvExpr : BVExpr w
  evalsAtAToms : M Expr
  expr : Expr -- `toExpr bvExpr`, cached

namespace BVAtAtoms

def of (x : Expr) : M (Option (BVAtAtoms w)) := do
  match x.getAppFnArgs with
  | (``BitVec.ofNat, #[_, valExpr]) =>
    let val := parseNatLit valExpr
    let bvVal := BitVec.ofNat w val
    let bvExpr := .const (BitVec.ofNat w val)
    let expr := mkApp2 (mkConst ``BVExpr.const) (toExpr w) (toExpr bvVal)
    -- Hopefully by rfl?
    let proof := do sorry
    return some ⟨bvExpr, proof, expr⟩
  | _ => return none

end BVAtAtoms

structure HoldsAtAtoms (α : Type) where
  bvExpr : α
  holdsAtAtoms : M Expr -- a proof that `expr.eval atomsFn = true`
  expr : Expr -- `toExpr bvExpr`, cached

namespace HoldsAtAtoms

-- TODO: we could store `evalFunc` in `HoldsAtAtoms` and maybe even fill it out with typeclass stuff
def mkEvalExpr (evalFunc : Name) (expr : Expr) : M Expr := do
  return mkApp2 (mkConst evalFunc) (← M.atomsAssignment) expr

partial def of (h : Expr) : M (Option (HoldsAtAtoms BVLogicalExpr)) := do
  -- TODO: naive approach, does not handle any boolean structure on top of our problem
  -- this is no issue for most cases but we *must* handle at least negation of preds
  -- for any proof by contradiction where the goal involves a bitvec expression.
  let some pred ← ofPred h | return none
  let bvExpr := .literal pred.bvExpr
  let expr := mkApp2 (mkConst ``BoolExpr.literal) (mkConst ``BVPred) pred.expr
  let proof := do
    let evalLogic ← mkEvalExpr ``BVLogicalExpr.eval expr
    let evalPred ← mkEvalExpr ``BVPred.eval expr
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
    | (``Eq, #[.app (.const ``BitVec []) widthExpr, lhs, rhs]) =>
      let width := parseNatLit widthExpr
      IO.println lhs
      IO.println rhs
      let some lhs ← BVAtAtoms.of lhs | return none
      let some rhs ← BVAtAtoms.of rhs | return none
      let bvExpr := .bin (w := width) lhs.bvExpr .eq rhs.bvExpr
      let expr := mkApp4 (mkConst ``BVPred.bin) widthExpr lhs.expr (mkConst ``BVBinPred.eq) rhs.expr
      /-
        TODO: This will become a proof that evaluating this predicate holds through a congruence argument:
        - h is of the form bv1 = bv2
        - we obtain proof from the parsing of bv1 and bv2 that evaluating their expressions (call them bv1' bv2')
          is equivalent to bv1 and bv2 respectively
        - we need a theorem that says (bv1 = bv2) (bv1 = bv1') (bv2 = bv2') : bv1' = bv2'
        - apply this theorem on h and the lemmas from the parsed BV expressions
      -/
      let proof := do sorry
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
