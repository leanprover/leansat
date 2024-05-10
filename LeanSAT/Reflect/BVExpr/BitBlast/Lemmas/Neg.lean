import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Add
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Const
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Not
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Neg

open AIG

namespace BVExpr
namespace bitblast

open BitVec

theorem blastNeg_eq_eval_getLsb (aig : AIG BVBit) (sub : BVExpr w) (assign : Assignment)
      (input : RefStream aig w)
      (hsub : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.getRef idx hidx, assign.toAIGAssignment⟧ = (sub.eval assign).getLsb idx)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastNeg aig input).aig, (blastNeg aig input).stream.getRef idx hidx, assign.toAIGAssignment⟧
          =
        (~~~(sub.eval assign) + 1#w).getLsb idx := by
  intro idx hidx
  unfold blastNeg
  dsimp
  rw [blastAdd_eq_eval_getLsb (lhs := (.un .not sub)) (rhs := (.const 1#w))]
  . simp
  . intro idx hidx
    simp only [RefStream.getRef_cast, Ref_cast', eval_un, BVUnOp.eval_not, getLsb_not, hidx,
      decide_True, Bool.true_and]
    rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastConst)]
    rw [blastNot_eq_eval_getLsb]
    rw [hsub]
  . intro idx hidx
    simp

end bitblast
end BVExpr
