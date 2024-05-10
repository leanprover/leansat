import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Not

open AIG

namespace BVExpr
namespace bitblast

@[simp]
theorem blastNot_eq_eval_getLsb (aig : AIG BVBit) (target : RefStream aig w)
    (assign : Assignment)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (blastNot aig target).aig,
          (blastNot aig target).stream.getRef idx hidx,
          assign.toAIGAssignment
        ⟧
          =
        !⟦
          aig,
          target.getRef idx hidx,
          assign.toAIGAssignment
         ⟧
        := by
  intro idx hidx
  unfold blastNot
  simp

end bitblast
end BVExpr
