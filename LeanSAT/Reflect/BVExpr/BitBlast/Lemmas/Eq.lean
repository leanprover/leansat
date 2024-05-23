import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Expr
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Eq

open AIG

namespace BVPred

theorem mkEq_denote_iff_eval_beq (aig : AIG BVBit) (pair : ExprPair) (assign : BVExpr.Assignment)
    : ⟦mkEq aig pair, assign.toAIGAssignment⟧
        ↔
      (pair.lhs.eval assign == pair.rhs.eval assign) := by
  rw [beq_iff_eq]
  unfold mkEq
  unfold mkEq.streamProc
  dsimp
  constructor
  . intro h
    apply BitVec.eq_of_getLsb_eq
    intro i
    simp only [RefStream.denote_fold_and, RefStream.denote_zip, RefStream.getRef_cast,
      denote_mkBEqCached, BVExpr.bitblast_denote_eq_eval_getLsb, beq_iff_eq] at h
    specialize h i.val i.isLt
    rw [AIG.LawfulStreamOperator.denote_input_stream (f := BVExpr.bitblast)] at h
    rw [← h]
    simp
  . intro h
    simp only [RefStream.denote_fold_and, RefStream.denote_zip, RefStream.getRef_cast,
      denote_mkBEqCached, BVExpr.bitblast_denote_eq_eval_getLsb, beq_iff_eq]
    intro idx hidx
    rw [AIG.LawfulStreamOperator.denote_input_stream (f := BVExpr.bitblast)]
    simp [h]

@[simp]
theorem mkEq_denote_eq_eval_beq (aig : AIG BVBit) (pair : ExprPair) (assign : BVExpr.Assignment)
    : ⟦mkEq aig pair, assign.toAIGAssignment⟧
        =
      (pair.lhs.eval assign == pair.rhs.eval assign) := by
  rw [Bool.eq_iff_iff]
  apply mkEq_denote_iff_eval_beq

end BVPred
