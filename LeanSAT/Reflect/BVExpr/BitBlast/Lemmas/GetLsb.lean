import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Expr
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.GetLsb

open AIG

namespace BVPred

@[simp]
theorem blastGetLsb_denote_eq_eval_getLsb (aig : AIG BVBit) (target : GetLsbTarget) (assign : BVExpr.Assignment)
    : ⟦blastGetLsb aig target, assign.toAIGAssignment⟧
        =
      (target.expr.eval assign).getLsb target.idx := by
  rcases target with ⟨expr, idx⟩
  unfold blastGetLsb
  dsimp
  split
  . simp
  . next h =>
    simp only [mkConstCached_eval_eq_mkConst_eval, denote_mkConst, Bool.false_eq]
    apply BitVec.getLsb_ge
    omega

end BVPred
