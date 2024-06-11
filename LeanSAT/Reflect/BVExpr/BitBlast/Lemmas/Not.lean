import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Not

open AIG

namespace BVExpr
namespace bitblast

variable [BEq α] [Hashable α] [DecidableEq α]

@[simp]
theorem blastNot_eq_eval_getLsb (aig : AIG α) (target : RefStream aig w)
    (assign : α → Bool)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (blastNot aig target).aig,
          (blastNot aig target).stream.getRef idx hidx,
          assign
        ⟧
          =
        !⟦
          aig,
          target.getRef idx hidx,
          assign
         ⟧
        := by
  intro idx hidx
  unfold blastNot
  simp

end bitblast
end BVExpr
