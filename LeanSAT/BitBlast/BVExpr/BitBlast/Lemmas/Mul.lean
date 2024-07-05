import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Add
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.ShiftLeft
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Const
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Mul

open AIG

namespace BVExpr

namespace bitblast
namespace blastMul

theorem go_eq_eval_getLsb {w : Nat} (aig : AIG BVBit) (curr : Nat) (hcurr : curr + 1 ≤ w)
    (acc : AIG.RefStream aig w) (lhs rhs : AIG.RefStream aig w) (lexpr rexpr : BitVec w) (assign : Assignment)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, lhs.getRef idx hidx, assign.toAIGAssignment⟧ = lexpr.getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, rhs.getRef idx hidx, assign.toAIGAssignment⟧ = rexpr.getLsb idx)
    (hacc : ∀ (idx : Nat) (hidx : idx < w),
                ⟦aig, acc.getRef idx hidx, assign.toAIGAssignment⟧
                  =
                (BitVec.mulRec lexpr rexpr curr).getLsb idx)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig (curr + 1) hcurr acc lhs rhs).aig,
          (go aig (curr + 1) hcurr acc lhs rhs).stream.getRef idx hidx,
          assign.toAIGAssignment
        ⟧
          =
        (BitVec.mulRec lexpr rexpr w).getLsb idx := by
  intro idx hidx
  generalize hgo: go aig (curr + 1) hcurr acc lhs rhs = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    rw [← hgo]
    rw [go_eq_eval_getLsb]
    . intro idx hidx
      simp only [RefStream.getRef_cast, Ref_cast']
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := RefStream.ite)]
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastAdd)]
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftLeftConst)]
      rw [hleft]
    . intro idx hidx
      simp only [RefStream.getRef_cast, Ref_cast']
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := RefStream.ite)]
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastAdd)]
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftLeftConst)]
      rw [hright]
    . intro idx hidx
      rw [BitVec.mulRec_succ_eq]
      simp only [RefStream.denote_ite, RefStream.getRef_cast, Ref_cast', BitVec.ofNat_eq_ofNat]
      split
      . next hdiscr =>
        have : rexpr.getLsb (curr + 1) = true := by
          rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastAdd)] at hdiscr
          rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftLeftConst)] at hdiscr
          rw [hright] at hdiscr
          exact hdiscr
        simp only [this, ↓reduceIte]
        rw [blastAdd_eq_eval_getLsb]
        . intros
          simp only [RefStream.getRef_cast, Ref_cast']
          rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftLeftConst)]
          rw [hacc]
        . intros
          simp only [blastShiftLeftConst_eq_eval_getLsb, BitVec.getLsb_shiftLeft]
          split
          . next hdiscr => simp [hdiscr]
          . next hidx hdiscr =>
            rw [hleft]
            simp [hdiscr, hidx]
      . next hdiscr =>
        have : rexpr.getLsb (curr + 1) = false := by
          rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastAdd)] at hdiscr
          rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftLeftConst)] at hdiscr
          rw [hright] at hdiscr
          simp [hdiscr]
        simp only [this, Bool.false_eq_true, ↓reduceIte, BitVec.add_zero]
        rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastAdd)]
        rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftLeftConst)]
        rw [hacc]
  . have : curr + 1 = w := by omega
    subst this
    rw [← hgo]
    rw [hacc]
    rw [BitVec.mulRec_succ_eq]
    have : rexpr.getLsb (curr + 1) = false := by
      apply BitVec.getLsb_ge
      omega
    simp [this]
termination_by w - curr
decreasing_by
  -- XXX: simp_wf sets unfoldPartialApp to true, this causes large performance issues here
  simp only [InvImage, WellFoundedRelation.rel, Nat.lt_wfRel, sizeOf_nat, Nat.lt_eq, gt_iff_lt]
  omega


end blastMul

theorem blastMul_eq_eval_getLsb (aig : AIG BVBit) (lhs rhs : BitVec w) (assign : Assignment)
      (input : BinaryRefStream aig w)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.getRef idx hidx, assign.toAIGAssignment⟧ = lhs.getLsb idx)
      (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.getRef idx hidx, assign.toAIGAssignment⟧ = rhs.getLsb idx)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastMul aig input).aig, (blastMul aig input).stream.getRef idx hidx, assign.toAIGAssignment⟧
          =
        (lhs * rhs).getLsb idx := by
  intro idx hidx
  rw [BitVec.getLsb_mul]
  generalize hb : blastMul aig input = res
  unfold blastMul at hb
  dsimp at hb
  split at hb
  . omega
  . next hne =>
    have := Nat.exists_eq_succ_of_ne_zero hne
    rcases this with ⟨w, hw⟩
    subst hw
    rw [← hb]
    rw [blastMul.go_eq_eval_getLsb]
    . intro idx hidx
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := RefStream.ite)]
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastConst)]
      . simp [hleft]
      . simp [Ref.hgate]
    . intro idx hidx
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := RefStream.ite)]
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastConst)]
      . simp [hright]
      . simp [Ref.hgate]
    . intro idx hidx
      rw [BitVec.mulRec_zero_eq]
      simp only [Nat.succ_eq_add_one, RefStream.denote_ite, BinaryRefStream.rhs_getRef_cast,
        Ref_cast', BinaryRefStream.lhs_getRef_cast, blastConst_eq_eval_getLsb,
        BitVec.ofNat_eq_ofNat, eval_const, BitVec.getLsb_zero, Bool.if_false_right,
        Bool.decide_eq_true]
      split
      . next heq =>
        rw [← hright] at heq
        . rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastConst)]
          rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastConst)]
          . simp [heq, hleft]
          . simp [Ref.hgate]
          . simp [Ref.hgate]
        . omega
      . next heq =>
        simp only [Bool.not_eq_true] at heq
        rw [← hright] at heq
        . rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastConst)]
          . simp [heq]
          . simp [Ref.hgate]
        . omega

end bitblast
end BVExpr
