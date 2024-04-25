import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Eq
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Neq

open AIG

namespace BVPred

theorem mkNeq_denote_iff_eval_neq (aig : AIG BVBit) (pair : ExprPair) (assign : BVExpr.Assignment)
    : ⟦mkNeq aig pair, assign.toAIGAssignment⟧
        ↔
      (pair.lhs.eval assign != pair.rhs.eval assign) := by
  unfold mkNeq
  simp

@[simp]
theorem mkNeq_denote_eq_eval_neq (aig : AIG BVBit) (pair : ExprPair) (assign : BVExpr.Assignment)
    : ⟦mkNeq aig pair, assign.toAIGAssignment⟧
        =
      (pair.lhs.eval assign != pair.rhs.eval assign) := by
  rw [Bool.eq_iff_iff]
  apply mkNeq_denote_iff_eval_neq

end BVPred
