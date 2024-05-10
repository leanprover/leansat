import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Neg
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Add
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Sub

open AIG

namespace BVExpr
namespace bitblast

theorem blastSub_eq_eval_getLsb (aig : AIG BVBit) (lhs rhs : BVExpr w) (assign : Assignment)
      (input : BinaryRefStream aig w)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.getRef idx hidx, assign.toAIGAssignment⟧ = (lhs.eval assign).getLsb idx)
      (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.getRef idx hidx, assign.toAIGAssignment⟧ = (rhs.eval assign).getLsb idx)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastSub aig input).aig, (blastSub aig input).stream.getRef idx hidx, assign.toAIGAssignment⟧
          =
        (lhs.eval assign - rhs.eval assign).getLsb idx := by
  intros idx hidx
  unfold blastSub
  dsimp
  rw [blastAdd_eq_eval_getLsb (lhs := lhs) (rhs := .un .neg rhs)]
  . simp [BitVec.sub_toAdd]
  . intro idx hidx
    rw [AIG.LawfulStreamOperator.denote_mem_prefix]
    . simp [hleft]
    . simp [Ref.hgate]
  . intro idx hidx
    rw [blastNeg_eq_eval_getLsb (sub := rhs)]
    . simp [BitVec.neg_eq_not_add]
    . simp [hright]

end bitblast
end BVExpr
