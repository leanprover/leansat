import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Const
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Var
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.ShiftLeft
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.ShiftRight
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Add
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Expr

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
