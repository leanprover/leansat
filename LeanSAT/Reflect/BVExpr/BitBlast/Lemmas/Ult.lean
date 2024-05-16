import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Expr
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Carry
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Not
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Ult

open AIG

namespace BVPred

@[simp]
theorem mkUlt_denote_eq_eval_ult (aig : AIG BVBit) (pair : ExprPair) (assign : BVExpr.Assignment)
    : ⟦mkUlt aig pair, assign.toAIGAssignment⟧
        =
      BitVec.ult (pair.lhs.eval assign) (pair.rhs.eval assign) := by
  rw [BitVec.ult_eq_not_carry]
  unfold mkUlt
  rcases pair with ⟨lhs, rhs⟩
  rename_i w
  simp only [denote_mkNotCached, denote_projected_entry']
  congr 1
  rw [BVExpr.bitblast.mkOverflowBit_eq_carry (input := ⟨w, _, _⟩) (lhs := lhs) (rhs := .un .not rhs)]
  . dsimp
    congr 1
    simp
  . dsimp
    intro idx hidx
    rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
    rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := BVExpr.bitblast.blastNot)]
    rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := BVExpr.bitblast)]
    simp only [RefStream.getRef_cast, Ref_cast']
    rw [BVExpr.bitblast_denote_eq_eval_getLsb]
    simp [Ref.hgate]
  . dsimp
    intro idx hidx
    rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
    . simp only [RefStream.getRef_cast, Ref_cast', BitVec.getLsb_not, hidx, decide_True, Bool.true_and]
      rw [BVExpr.bitblast.blastNot_eq_eval_getLsb]
      rw [BVExpr.bitblast_denote_eq_eval_getLsb]
    . simp [Ref.hgate]

end BVPred
