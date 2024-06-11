import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Carry
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Not
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Ult

open AIG

namespace BVPred

variable [BEq α] [Hashable α] [DecidableEq α]

theorem mkUlt_denote_eq_eval_ult (aig : AIG α) (lhs rhs : BitVec w) (input : BinaryRefStream aig w)
    (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.getRef idx hidx, assign⟧ = lhs.getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.getRef idx hidx, assign⟧ = rhs.getLsb idx)
  : ⟦
      (mkUlt aig input).aig,
      (mkUlt aig input).ref,
      assign
    ⟧
      =
    BitVec.ult lhs rhs := by
  rw [BitVec.ult_eq_not_carry]
  unfold mkUlt
  simp only [denote_projected_entry, denote_mkNotCached, denote_projected_entry']
  congr 1
  rw [BVExpr.bitblast.mkOverflowBit_eq_carry (input := ⟨w, _, _⟩) (lhs := lhs) (rhs := ~~~rhs)]
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

end BVPred
