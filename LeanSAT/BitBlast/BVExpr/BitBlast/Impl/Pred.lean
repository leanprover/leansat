/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Eq
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Ult
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.GetLsb
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Expr

namespace BVPred

def bitblast (aig : AIG BVBit) (pred : BVPred) : AIG.Entrypoint BVBit :=
  match pred with
  | .bin lhs op rhs =>
    let res := lhs.bitblast aig
    let aig := res.aig
    let lhsRefs := res.stream
    let res := rhs.bitblast aig
    let aig := res.aig
    let rhsRefs := res.stream
    let lhsRefs := lhsRefs.cast <| by
      simp (config := { zetaDelta := true }) only
      apply AIG.LawfulStreamOperator.le_size (f := BVExpr.bitblast)
    match op with
    | .eq => mkEq aig ⟨lhsRefs, rhsRefs⟩
    | .ult => mkUlt aig ⟨lhsRefs, rhsRefs⟩
  | .getLsb expr idx =>
    /-
    Note: This blasts the entire rexpression up to `w` despite only needing it up to `idx`.
    However the vast majority of operations are interested in all bits so the API is currently
    not designed to support this use case.
    -/
    let res := expr.bitblast aig
    let aig := res.aig
    let refs := res.stream
    blastGetLsb aig ⟨refs, idx⟩

theorem bitblast_le_size (aig : AIG BVBit) (pred : BVPred)
    : aig.decls.size ≤ (bitblast aig pred).aig.decls.size := by
  cases pred with
  | bin lhs op rhs =>
    cases op with
    | eq =>
      simp [bitblast]
      apply AIG.LawfulOperator.le_size_of_le_aig_size (f := mkEq)
      apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
      apply AIG.LawfulStreamOperator.le_size (f := BVExpr.bitblast)
    | ult =>
      simp [bitblast]
      apply AIG.LawfulOperator.le_size_of_le_aig_size (f := mkUlt)
      apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
      apply AIG.LawfulStreamOperator.le_size (f := BVExpr.bitblast)
  | getLsb expr idx =>
    simp only [bitblast]
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := blastGetLsb)
    apply AIG.LawfulStreamOperator.le_size (f := BVExpr.bitblast)

theorem bitblast_decl_eq (aig : AIG BVBit) (pred : BVPred) {h : idx < aig.decls.size} :
    have := bitblast_le_size aig pred
    (bitblast aig pred).aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  cases pred with
  | bin lhs op rhs =>
    cases op with
    | eq =>
      simp only [bitblast]
      rw [AIG.LawfulOperator.decl_eq (f := mkEq)]
      rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast)]
      rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast)]
      . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
        assumption
      . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
        apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
        assumption
    | ult =>
      simp only [bitblast]
      rw [AIG.LawfulOperator.decl_eq (f := mkUlt)]
      rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast)]
      rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast)]
      . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
        assumption
      . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
        apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
        assumption
  | getLsb expr idx =>
    simp only [bitblast]
    rw [AIG.LawfulOperator.decl_eq (f := blastGetLsb)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast)]
    apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
    assumption

instance : AIG.LawfulOperator BVBit (fun _ => BVPred) bitblast where
  le_size := bitblast_le_size
  decl_eq := by intros; apply bitblast_decl_eq

end BVPred
