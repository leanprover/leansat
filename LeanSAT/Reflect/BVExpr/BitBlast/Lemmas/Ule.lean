import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Expr
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Carry
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Not
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Ule

open AIG

namespace BVPred

@[simp]
theorem mkUle_denote_eq_eval_ult (aig : AIG BVBit) (pair : ExprPair) (assign : BVExpr.Assignment)
    : ⟦mkUle aig pair, assign.toAIGAssignment⟧
        =
      BitVec.ule (pair.lhs.eval assign) (pair.rhs.eval assign) := by
  rw [BitVec.ule_eq_carry]
  unfold mkUle
  rcases pair with ⟨lhs, rhs⟩
  rename_i w
  dsimp
  rw [BVExpr.bitblast.mkOverflowBit_eq_carry (input := ⟨w, _, _⟩) (lhs := rhs) (rhs := .un .not lhs)]
  . dsimp
    congr 1
    simp
  . dsimp
    intro idx hidx
    rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
    . simp only [RefStream.getRef_cast, Ref_cast']
      rw [BVExpr.bitblast_denote_eq_eval_getLsb]
    . simp [Ref.hgate]
  . dsimp
    intro idx hidx
    rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
    rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := BVExpr.bitblast)]
    . simp [hidx]
      rw [BVExpr.bitblast.blastNot_eq_eval_getLsb]
      rw [BVExpr.bitblast_denote_eq_eval_getLsb]
    . simp [Ref.hgate]

end BVPred
