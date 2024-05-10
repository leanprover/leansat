import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Eq
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Pred

open AIG

namespace BVPred

@[simp]
theorem bitblast_denote_eq_eval (aig : AIG BVBit) (pred : BVPred) (assign : BVExpr.Assignment)
    : ⟦bitblast aig pred, assign.toAIGAssignment⟧
        =
      pred.eval assign := by
  cases pred with
  | bin lhs op rhs =>
    cases op with
    | eq => simp [bitblast]

end BVPred
