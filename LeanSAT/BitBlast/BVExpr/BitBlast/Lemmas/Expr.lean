/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Const
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Var
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Not
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.ShiftLeft
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.ShiftRight
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Add
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.ZeroExtend
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Append
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Extract
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.RotateLeft
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.RotateRight
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.SignExtend
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Expr
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Mul

open AIG

namespace BVExpr
namespace bitblast

theorem go_val_eq_bitblast (aig : AIG BVBit) (expr : BVExpr w)
    : (go aig expr).val = bitblast aig expr := by
  rfl

theorem go_denote_mem_prefix (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment) (start : Nat)
    (hstart)
  : ⟦
      (go aig expr).val.aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply (go aig expr).property⟩,
      assign.toAIGAssignment
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign.toAIGAssignment⟧ := by
  apply denote.eq_of_aig_eq (entry := ⟨aig, start,hstart⟩)
  apply IsPrefix.of
  . intros
    apply go_decl_eq
  . intros
    apply (go aig expr).property

theorem go_denote_eq_eval_getLsb (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦(go aig expr).val.aig, (go aig expr).val.stream.getRef idx hidx, assign.toAIGAssignment⟧
          =
        (expr.eval assign).getLsb idx := by
  intro idx hidx
  induction expr generalizing aig idx with
  | const =>
    simp [go, blastConst_eq_eval_getLsb]
  | var =>
    simp [go, hidx, blastVar_eq_eval_getLsb]
  | zeroExtend v inner ih =>
    simp only [go, blastZeroExtend_eq_eval_getLsb, ih, dite_eq_ite, Bool.if_false_right,
      eval_zeroExtend, BitVec.getLsb_zeroExtend, hidx, decide_True, Bool.true_and,
      Bool.and_iff_right_iff_imp, decide_eq_true_eq]
    apply BitVec.lt_of_getLsb
  | append lhs rhs lih rih =>
    rename_i lw rw
    simp only [go, blastAppend_eq_eval_getLsb, RefStream.getRef_cast, Ref_cast', eval_append,
      BitVec.getLsb_append]
    split
    . next hsplit =>
      simp only [hsplit, decide_True, cond_true]
      rw [rih]
    . next hsplit =>
      simp only [hsplit, decide_False, cond_false]
      rw [go_denote_mem_prefix, lih]
  | signExtend v inner ih =>
    rename_i originalWidth
    generalize hgo : (go aig (signExtend v inner)).val = res
    unfold go at hgo
    dsimp at hgo
    have : 0 ≤ originalWidth := by omega
    cases Nat.eq_or_lt_of_le this with
    | inl heq =>
      rw [blastSignExtend_empty_eq_zeroExtend] at hgo
      . rw [← hgo]
        simp only [eval_signExtend]
        rw [BitVec.signExtend_eq_not_zeroExtend_not_of_msb_false]
        . simp only [blastZeroExtend_eq_eval_getLsb, ih, dite_eq_ite, Bool.if_false_right,
            BitVec.getLsb_zeroExtend, hidx, decide_True, Bool.true_and, Bool.and_iff_right_iff_imp,
            decide_eq_true_eq]
          apply BitVec.lt_of_getLsb
        . subst heq
          rw [BitVec.msb_zero_length]
      . simp [heq]
    | inr hlt =>
      rw [← hgo]
      rw [blastSignExtend_eq_eval_getLsb]
      simp only [eval_signExtend]
      rw [BitVec.getLsb_signExtend]
      . simp only [hidx, decide_True, Bool.true_and]
        split
        . rw [ih]
        . rw [BitVec.msb_eq_getLsb_last]
          rw [ih]
      . dsimp; omega
  | extract hi lo inner ih =>
    simp only [go, blastExtract_eq_eval_getLsb, Bool.if_false_right, eval_extract,
      BitVec.getLsb_extract]
    have : idx ≤ hi - lo := by omega
    simp only [this, decide_True, Bool.true_and]
    split
    . next hsplit =>
      rw [ih]
    . apply Eq.symm
      apply BitVec.getLsb_ge
      omega
  | shiftLeft lhs rhs lih rih =>
    simp only [go, eval_shiftLeft]
    apply blastShiftLeft_eq_eval_getLsb
    . intros
      dsimp
      rw [go_denote_mem_prefix]
      rw [← lih (aig := aig)]
      . simp
      . assumption
      . simp [Ref.hgate]
    . intros
      rw [← rih]
  | bin lhs op rhs lih rih =>
    cases op with
    | and =>
      simp only [go, RefStream.denote_zip, denote_mkAndCached, rih, eval_bin, BVBinOp.eval_and,
        BitVec.getLsb_and]
      simp only [go_val_eq_bitblast, RefStream.getRef_cast]
      rw [AIG.LawfulStreamOperator.denote_input_stream (f := bitblast)]
      rw [← go_val_eq_bitblast]
      rw [lih]
    | or =>
      simp only [go, RefStream.denote_zip, denote_mkOrCached, rih, eval_bin, BVBinOp.eval_or,
        BitVec.getLsb_or]
      simp only [go_val_eq_bitblast, RefStream.getRef_cast]
      rw [AIG.LawfulStreamOperator.denote_input_stream (f := bitblast)]
      rw [← go_val_eq_bitblast]
      rw [lih]
    | xor =>
      simp only [go, RefStream.denote_zip, denote_mkXorCached, rih, eval_bin, BVBinOp.eval_xor,
        BitVec.getLsb_xor]
      simp only [go_val_eq_bitblast, RefStream.getRef_cast]
      rw [AIG.LawfulStreamOperator.denote_input_stream (f := bitblast)]
      rw [← go_val_eq_bitblast]
      rw [lih]
    | add =>
      simp only [go, eval_bin, BVBinOp.eval_add]
      apply blastAdd_eq_eval_getLsb
      . intros
        dsimp
        rw [go_denote_mem_prefix]
        rw [← lih (aig := aig)]
        . simp
        . assumption
        . simp [Ref.hgate]
      . intros
        rw [← rih]
    | mul =>
      simp only [go, eval_bin, BVBinOp.eval_mul]
      apply blastMul_eq_eval_getLsb
      . intros
        dsimp
        rw [go_denote_mem_prefix]
        rw [← lih (aig := aig)]
        . simp
        . assumption
        . simp [Ref.hgate]
      . intros
        rw [← rih]
  | un op expr ih =>
    cases op with
    | not => simp [go, ih, hidx]
    | shiftLeftConst => simp [go, ih, hidx]
    | shiftRightConst =>
      simp only [go, blastShiftRight_eq_eval_getLsb, ih, dite_eq_ite, Bool.if_false_right, eval_un,
        BVUnOp.eval_shiftRightConst, BitVec.getLsb_ushiftRight, Bool.and_iff_right_iff_imp,
        decide_eq_true_eq]
      intro h
      apply BitVec.lt_of_getLsb
      assumption
    | rotateLeft => simp [go, ih, hidx]
    | rotateRight => simp [go, ih, hidx]
    | arithShiftRightConst n =>
      rename_i w
      have : ¬(w ≤ idx) := by omega
      simp [go, ih, this, BitVec.getLsb_sshiftRight, BitVec.msb_eq_getLsb_last ]

end bitblast
@[simp]
theorem bitblast_denote_eq_eval_getLsb (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦(bitblast aig expr).aig, (bitblast aig expr).stream.getRef idx hidx, assign.toAIGAssignment⟧
          =
        (expr.eval assign).getLsb idx
    := by
  intros
  rw [← bitblast.go_val_eq_bitblast]
  rw [bitblast.go_denote_eq_eval_getLsb]

end BVExpr
