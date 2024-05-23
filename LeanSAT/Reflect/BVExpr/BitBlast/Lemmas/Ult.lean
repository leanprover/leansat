import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Expr
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Carry
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Not
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Ult

open AIG

namespace BVPred

theorem mkUlt.streamProc_denote_eq_eval_ult (aig : AIG BVBit) (lhs rhs : BVExpr w) (input : BinaryRefStream aig w)
    (assign : BVExpr.Assignment)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.getRef idx hidx, assign.toAIGAssignment⟧ = (lhs.eval assign).getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.getRef idx hidx, assign.toAIGAssignment⟧ = (rhs.eval assign).getLsb idx)
  : ⟦
      (mkUlt.streamProc aig input).aig,
      (mkUlt.streamProc aig input).ref,
      assign.toAIGAssignment
    ⟧
      =
    BitVec.ult (lhs.eval assign) (rhs.eval assign) := by
  rw [BitVec.ult_eq_not_carry]
  unfold mkUlt.streamProc
  simp only [denote_projected_entry, denote_mkNotCached, denote_projected_entry']
  congr 1
  rw [BVExpr.bitblast.mkOverflowBit_eq_carry (input := ⟨w, _, _⟩) (lhs := lhs) (rhs := .un .not rhs)]
  . simp
  . dsimp
    intro idx hidx
    rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
    rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := BVExpr.bitblast.blastNot)]
    apply hleft
    assumption
  . dsimp
    intro idx hidx
    rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
    . simp only [RefStream.getRef_cast, Ref_cast', BitVec.getLsb_not, hidx, decide_True,
        Bool.true_and]
      rw [BVExpr.bitblast.blastNot_eq_eval_getLsb]
      congr 1
      apply hright
    . simp [Ref.hgate]


@[simp]
theorem mkUlt_denote_eq_eval_ult (aig : AIG BVBit) (pair : ExprPair) (assign : BVExpr.Assignment)
    : ⟦mkUlt aig pair, assign.toAIGAssignment⟧
        =
      BitVec.ult (pair.lhs.eval assign) (pair.rhs.eval assign) := by
  unfold mkUlt
  rcases pair with ⟨lhs, rhs⟩
  rename_i w
  simp
  rw [mkUlt.streamProc_denote_eq_eval_ult (lhs := lhs) (rhs := rhs)]
  . intros
    rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := BVExpr.bitblast)]
    . simp only [RefStream.getRef_cast, Ref_cast]
      rw [BVExpr.bitblast_denote_eq_eval_getLsb]
    . simp [Ref.hgate]
  . intros
    simp
