/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Frontend.BVDecide.ReifiedBVExpr

/-!
Provides the logic for reifying expressions consisting of predicates over `BitVec`s.
-/

namespace LeanSAT
namespace BVDecide

open Lean
open Lean.Meta
open Lean.Elab.Tactic.BVDecide

/--
A reified version of an `Expr` representing a `BVPred`.
-/
structure ReifiedBVPred where
  /--
  The reified expression.
  -/
  bvPred : BVPred
  /--
  A proof that `bvPred.eval atomsAssignment = originalBVPredExpr`.
  -/
  evalsAtAtoms : M Expr
  /--
  A cache for `toExpr bvPred`
  -/
  expr : Expr

namespace ReifiedBVPred

theorem beq_congr (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    (lhs' == rhs') = (lhs == rhs) := by
  simp[*]

theorem ult_congr (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    (BitVec.ult lhs' rhs') = (BitVec.ult lhs rhs) := by
  simp[*]

theorem getLsb_congr (i : Nat) (w : Nat) (e e' : BitVec w) (h : e' = e) :
    (e'.getLsb i) = (e.getLsb i) := by
  simp[*]

theorem ofBool_congr (b : Bool) (e' : BitVec 1) (h : e' = BitVec.ofBool b) : e'.getLsb 0 = b := by
  cases b <;> simp [h]

/--
Reify an `Expr` that is a proof of a predicate about `BitVec`.
-/
def of (t : Expr) : M (Option ReifiedBVPred) := do
  match_expr t with
  | BEq.beq α _ lhsExpr rhsExpr =>
    let_expr BitVec _ := α | return none
    binaryReflection lhsExpr rhsExpr .eq ``beq_congr
  | BitVec.ult _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .ult ``ult_congr
  | BitVec.getLsb _ subExpr idxExpr =>
    let some sub ← ReifiedBVExpr.of subExpr | return none
    let some idx ← getNatValue? idxExpr | return none
    let bvExpr : BVPred := .getLsb sub.bvExpr idx
    let expr := mkApp3 (mkConst ``BVPred.getLsb) (toExpr sub.width) sub.expr idxExpr
    let proof := do
      let subEval ← ReifiedBVExpr.mkEvalExpr sub.width sub.expr
      let subProof ← sub.evalsAtAtoms
      return mkApp5
        (mkConst ``getLsb_congr)
        idxExpr
        (toExpr sub.width)
        subExpr
        subEval
        subProof
    return some ⟨bvExpr, proof, expr⟩
  | _ =>
    /-
    Idea: we have t : Bool here, let's construct:
      BitVec.ofBool t : BitVec 1
    as an atom. Then construct the BVPred corresponding to
      BitVec.getLsb (BitVec.ofBool t) 0 : Bool
    We can prove that this is equivalent to `t`. This allows us to have boolean variables in BVPred.
    -/
    let ty ← inferType t
    let_expr Bool := ty | return none
    let atom ← ReifiedBVExpr.mkAtom (mkApp (mkConst ``BitVec.ofBool) t) 1
    let bvExpr : BVPred := .getLsb atom.bvExpr 0
    let expr := mkApp3 (mkConst ``BVPred.getLsb) (toExpr 1) atom.expr (toExpr 0)
    let proof := do
      let atomEval ← ReifiedBVExpr.mkEvalExpr atom.width atom.expr
      let atomProof ← atom.evalsAtAtoms
      return mkApp3
        (mkConst ``ofBool_congr)
        t
        atomEval
        atomProof
    return some ⟨bvExpr, proof, expr⟩
where
  binaryReflection (lhsExpr rhsExpr : Expr) (pred : BVBinPred) (congrThm : Name) :
      M (Option ReifiedBVPred) := do
    let some lhs ← ReifiedBVExpr.of lhsExpr | return none
    let some rhs ← ReifiedBVExpr.of rhsExpr | return none
    if h:lhs.width = rhs.width then
      let bvExpr : BVPred := .bin (w := lhs.width) lhs.bvExpr pred (h ▸ rhs.bvExpr)
      let expr :=
        mkApp4
          (mkConst ``BVPred.bin)
          (toExpr lhs.width)
          lhs.expr
          (toExpr pred)
          rhs.expr
      let proof := do
        let lhsEval ← ReifiedBVExpr.mkEvalExpr lhs.width lhs.expr
        let lhsProof ← lhs.evalsAtAtoms
        let rhsEval ← ReifiedBVExpr.mkEvalExpr rhs.width rhs.expr
        let rhsProof ← rhs.evalsAtAtoms
        return mkApp7
          (mkConst congrThm)
          (toExpr lhs.width)
          lhsExpr rhsExpr lhsEval rhsEval
          lhsProof
          rhsProof
      return some ⟨bvExpr, proof, expr⟩
    else
      return none


end ReifiedBVPred

end BVDecide
end LeanSAT
