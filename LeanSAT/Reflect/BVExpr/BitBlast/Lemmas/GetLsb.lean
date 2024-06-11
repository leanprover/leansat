import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.GetLsb

open AIG

namespace BVPred

variable [BEq α] [Hashable α] [DecidableEq α]

@[simp]
theorem blastGetLsb_denote_eq_eval_getLsb (aig : AIG α) (target : GetLsbTarget aig) (assign : α → Bool)
    : ⟦blastGetLsb aig target, assign⟧
        =
      if h:target.idx < target.w then
        ⟦aig, target.stream.getRef target.idx h, assign⟧
      else
        false := by
  rcases target with ⟨expr, idx⟩
  unfold blastGetLsb
  dsimp
  split <;> simp

end BVPred
