/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Frontend.BVDecide.ReifiedBVPred

namespace LeanSAT
namespace BVDecide

open Lean
open Lean.Elab.Tactic.BVDecide

/--
A reified version of an `Expr` representing a `BVLogicalExpr`.
-/
structure ReifiedBVLogical where
  /--
  The reified expression.
  -/
  bvExpr : BVLogicalExpr
  /--
  A proof that `bvExpr.eval atomsAssignment = originalBVLoigcalExpr`.
  -/
  evalsAtAtoms : M Expr
  /--
  A cache for `toExpr bvExpr`
  -/
  expr : Expr

namespace ReifiedBVLogical

def mkRefl (expr : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) expr

def mkTrans (x y z : Expr) (hxy hyz : Expr) : Expr :=
  mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``Bool) x y z hxy hyz

def mkEvalExpr (expr : Expr) : M Expr := do
  return mkApp2 (mkConst ``BVLogicalExpr.eval) (← M.atomsAssignment) expr

theorem not_congr (x x' : Bool) (h : x' = x) : (!x') = (!x) := by
  simp[*]

theorem and_congr (lhs rhs lhs' rhs' : Bool) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    (lhs' && rhs') = (lhs && rhs) := by
  simp[*]

theorem or_congr (lhs rhs lhs' rhs' : Bool) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    (lhs' || rhs') = (lhs || rhs) := by
  simp[*]

theorem xor_congr (lhs rhs lhs' rhs' : Bool) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    (xor lhs' rhs') = (xor lhs rhs) := by
  simp[*]

theorem beq_congr (lhs rhs lhs' rhs' : Bool) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    (lhs' == rhs') = (lhs == rhs) := by
  simp[*]

partial def of (t : Expr) : M (Option ReifiedBVLogical) := do
  match_expr t with
  | Bool.true =>
    let boolExpr := .const true
    let expr := mkApp2 (mkConst ``BoolExpr.const) (mkConst ``BVPred) (toExpr Bool.true)
    let proof := return mkRefl (mkConst ``Bool.true)
    return some ⟨boolExpr, proof, expr⟩
  | Bool.false =>
    let boolExpr := .const false
    let expr := mkApp2 (mkConst ``BoolExpr.const) (mkConst ``BVPred) (toExpr Bool.false)
    let proof := return mkRefl (mkConst ``Bool.false)
    return some ⟨boolExpr, proof, expr⟩
  | not subExpr =>
    let some sub ← of subExpr | return none
    let boolExpr := .not sub.bvExpr
    let expr := mkApp2 (mkConst ``BoolExpr.not) (mkConst ``BVPred) sub.expr
    let proof := do
      let subEvalExpr ← mkEvalExpr sub.expr
      let subProof ← sub.evalsAtAtoms
      return mkApp3 (mkConst ``not_congr) subExpr subEvalExpr subProof
    return some ⟨boolExpr, proof, expr⟩
  | or lhsExpr rhsExpr => gateReflection lhsExpr rhsExpr .or ``or_congr
  | and lhsExpr rhsExpr => gateReflection lhsExpr rhsExpr .and ``and_congr
  | xor lhsExpr rhsExpr => gateReflection lhsExpr rhsExpr .xor ``xor_congr
  | BEq.beq α _ lhsExpr rhsExpr =>
    match_expr α with
    | Bool => gateReflection lhsExpr rhsExpr .beq ``beq_congr
    | BitVec _ => goPred t
    | _ => return none
  | _ => goPred t
where
  gateReflection (lhsExpr rhsExpr : Expr) (gate : Gate) (congrThm : Name) :
      M (Option ReifiedBVLogical) := do
    let some lhs ← of lhsExpr | return none
    let some rhs ← of rhsExpr | return none
    let boolExpr := .gate  gate lhs.bvExpr rhs.bvExpr
    let expr :=
      mkApp4
        (mkConst ``BoolExpr.gate)
        (mkConst ``BVPred)
        (toExpr gate)
        lhs.expr
        rhs.expr
    let proof := do
      let lhsEvalExpr ← mkEvalExpr lhs.expr
      let rhsEvalExpr ← mkEvalExpr rhs.expr
      let lhsProof ← lhs.evalsAtAtoms
      let rhsProof ← rhs.evalsAtAtoms
      return mkApp6
        (mkConst congrThm)
        lhsExpr rhsExpr
        lhsEvalExpr rhsEvalExpr
        lhsProof rhsProof
    return some ⟨boolExpr, proof, expr⟩

  goPred (t : Expr) : M (Option ReifiedBVLogical) := do
    let some bvPred ← ReifiedBVPred.of t | return none
    let boolExpr := .literal bvPred.bvPred
    let expr := mkApp2 (mkConst ``BoolExpr.literal) (mkConst ``BVPred) bvPred.expr
    let proof := bvPred.evalsAtAtoms
    return some ⟨boolExpr, proof, expr⟩

end ReifiedBVLogical

end BVDecide
end LeanSAT
