import LeanSAT.Reflect.BVExpr.BitBlast

open AIG

namespace BVExpr

def Assignment.toAIGAssignment (assign : Assignment) : BVBit → Bool :=
  fun bit => (assign.getD bit.var).bv.getLsb bit.idx

@[simp]
theorem Assignment.toAIGAssignment_apply (assign : Assignment) (bit : BVBit)
    : assign.toAIGAssignment bit = (assign.getD bit.var).bv.getLsb bit.idx := by
  rfl

namespace bitblast

namespace blastConst

theorem go_getRef_aux (aig : AIG BVBit) (c : BitVec w) (curr : Nat) (hcurr : curr ≤ w)
    (s : AIG.RefStream aig curr)
    -- The hfoo here is a trick to make the dependent type gods happy
    : ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig curr s c hcurr).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig curr s c hcurr = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    rw [← hgo]
    intro hfoo
    rw [go_getRef_aux]
    rw [AIG.RefStream.getRef_push_ref_lt]
    . simp only [Ref.cast, Ref.mk.injEq]
      rw [AIG.RefStream.getRef_cast]
      . simp
      . assumption
    . apply go_le_size
  . dsimp at hgo
    rw [← hgo]
    simp only [Nat.le_refl, RefStream.getRef, Ref_cast', Ref.mk.injEq, true_implies]
    congr
    . omega
    . simp
termination_by w - curr

theorem go_getRef (aig : AIG BVBit) (c : BitVec w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx : idx < curr),
        (go aig curr s c hcurr).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_getRef_aux

theorem go_denote_mem_prefix (aig : AIG BVBit) (idx : Nat) (hidx)
    (s : AIG.RefStream aig idx) (c : BitVec w) (start : Nat) (hstart)
  : ⟦
      (go aig idx s c hidx).aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply go_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign⟧ := by
  apply denote.eq_of_aig_eq (entry := ⟨aig, start,hstart⟩)
  apply IsPrefix.of
  . intros
    apply go_decl_eq
  . intros
    apply go_le_size

theorem go_eq_eval_getLsb (aig : AIG BVBit) (c : BitVec w) (assign : Assignment)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx1 : idx < w) (hidx2 : curr ≤ idx),
        ⟦
          (go aig curr s c hcurr).aig,
          (go aig curr s c hcurr).stream.getRef idx hidx1,
          assign.toAIGAssignment
        ⟧
          =
        ((BVExpr.const c).eval assign).getLsb idx := by
  intro idx hidx1 hidx2
  generalize hgo : go aig curr s c hcurr = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      rw [← hgo]
      rw [go_getRef]
      rw [AIG.RefStream.getRef_push_ref_eq']
      . rw [← heq]
        rw [go_denote_mem_prefix]
        . simp
        . simp [Ref.hgate]
      . rw [heq]
    | inr =>
      rw [← hgo]
      dsimp
      rw [go_eq_eval_getLsb]
      . simp
      . omega
  . omega
termination_by w - curr

end blastConst

theorem blastConst_eq_eval_getLsb (aig : AIG BVBit) (c : BitVec w) (assign : Assignment)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastConst aig c).aig, (blastConst aig c).stream.getRef idx hidx, assign.toAIGAssignment⟧
          =
        ((BVExpr.const c).eval assign).getLsb idx := by
  intros
  apply blastConst.go_eq_eval_getLsb
  omega

namespace blastVar

theorem go_getRef_aux (aig : AIG BVBit) (a : Nat)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    -- The hfoo here is a trick to make the dependent type gods happy
    : ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go w aig curr s a hcurr).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go w aig curr s a hcurr = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    rw [← hgo]
    intro hfoo
    rw [go_getRef_aux]
    rw [AIG.RefStream.getRef_push_ref_lt]
    . simp only [Ref.cast, Ref.mk.injEq]
      rw [AIG.RefStream.getRef_cast]
      . simp
      . assumption
    . apply go_le_size
  . dsimp at hgo
    rw [← hgo]
    simp only [Nat.le_refl, RefStream.getRef, Ref_cast', Ref.mk.injEq, true_implies]
    congr
    . omega
    . simp
termination_by w - curr

theorem go_getRef (aig : AIG BVBit) (a : Nat)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx : idx < curr),
        (go w aig curr s a hcurr).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_getRef_aux

theorem go_denote_mem_prefix (aig : AIG BVBit) (idx : Nat) (hidx)
    (s : AIG.RefStream aig idx) (a : Nat) (start : Nat) (hstart)
  : ⟦
      (go w aig idx s a hidx).aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply go_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign⟧ := by
  apply denote.eq_of_aig_eq (entry := ⟨aig, start,hstart⟩)
  apply IsPrefix.of
  . intros
    apply go_decl_eq
  . intros
    apply go_le_size

theorem go_eq_eval_getLsb (aig : AIG BVBit) (a : Nat) (assign : Assignment)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx1 : idx < w) (hidx2 : curr ≤ idx),
        ⟦
          (go w aig curr s a hcurr).aig,
          (go w aig curr s a hcurr).stream.getRef idx hidx1,
          assign.toAIGAssignment
        ⟧
          =
        ((BVExpr.var (w := w) a).eval assign).getLsb idx := by
  intro idx hidx1 hidx2
  generalize hgo : go w aig curr s a hcurr = res
  unfold go at hgo
  split at hgo
  . next hlt =>
    dsimp at hgo
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      rw [← hgo]
      rw [go_getRef]
      rw [AIG.RefStream.getRef_push_ref_eq']
      . rw [← heq]
        rw [go_denote_mem_prefix]
        . simp [hlt]
        . simp [Ref.hgate]
      . rw [heq]
    | inr =>
      rw [← hgo]
      dsimp
      rw [go_eq_eval_getLsb]
      . simp
      . omega
  . omega
termination_by w - curr

end blastVar

theorem blastVar_eq_eval_getLsb (aig : AIG BVBit) (var : BVVar w) (assign : Assignment)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastVar aig var).aig, (blastVar aig var).stream.getRef idx hidx, assign.toAIGAssignment⟧
          =
        ((BVExpr.var (w := w) var.ident).eval assign).getLsb idx := by
  intros
  apply blastVar.go_eq_eval_getLsb
  omega

theorem go_val_eq_bitblast (aig : AIG BVBit) (expr : BVExpr w)
    : (go aig expr).val = bitblast aig expr := by
  rfl

theorem go_denote_eq_eval_getLsb (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦(go aig expr).val.aig, (go aig expr).val.stream.getRef idx hidx, assign.toAIGAssignment⟧
          =
        (expr.eval assign).getLsb idx := by
  intro idx hidx
  induction expr generalizing aig with
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
  | un op expr ih =>
    cases op with
    | not => simp [go, ih, hidx]

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

namespace BVPred

theorem mkEq_denote_iff_eval_beq (aig : AIG BVBit) (pair : ExprPair) (assign : BVExpr.Assignment)
    : ⟦mkEq aig pair, assign.toAIGAssignment⟧
        ↔
      (pair.lhs.eval assign == pair.rhs.eval assign) := by
  rw [beq_iff_eq]
  unfold mkEq
  dsimp
  constructor
  . intro h
    apply BitVec.eq_of_getLsb_eq
    intro i
    simp only [RefStream.denote_fold_and, RefStream.denote_zip, RefStream.getRef_cast,
      denote_mkBEqCached, BVExpr.bitblast_denote_eq_eval_getLsb, beq_iff_eq] at h
    specialize h i.val i.isLt
    rw [AIG.LawfulStreamOperator.denote_input_stream (f := BVExpr.bitblast)] at h
    rw [← h]
    simp
  . intro h
    simp only [RefStream.denote_fold_and, RefStream.denote_zip, RefStream.getRef_cast,
      denote_mkBEqCached, BVExpr.bitblast_denote_eq_eval_getLsb, beq_iff_eq]
    intro idx hidx
    rw [AIG.LawfulStreamOperator.denote_input_stream (f := BVExpr.bitblast)]
    simp [h]

@[simp]
theorem mkEq_denote_eq_eval_beq (aig : AIG BVBit) (pair : ExprPair) (assign : BVExpr.Assignment)
    : ⟦mkEq aig pair, assign.toAIGAssignment⟧
        =
      (pair.lhs.eval assign == pair.rhs.eval assign) := by
  rw [Bool.eq_iff_iff]
  apply mkEq_denote_iff_eval_beq

theorem mkNeq_denote_iff_eval_neq (aig : AIG BVBit) (pair : ExprPair) (assign : BVExpr.Assignment)
    : ⟦mkNeq aig pair, assign.toAIGAssignment⟧
        ↔
      (pair.lhs.eval assign != pair.rhs.eval assign) := by
  unfold mkNeq
  simp

@[simp]
theorem mkNeq_denote_eq_eval_neq (aig : AIG BVBit) (pair : ExprPair) (assign : BVExpr.Assignment)
    : ⟦mkNeq aig pair, assign.toAIGAssignment⟧
        =
      (pair.lhs.eval assign != pair.rhs.eval assign) := by
  rw [Bool.eq_iff_iff]
  apply mkNeq_denote_iff_eval_neq

@[simp]
theorem bitblast_denote_eq_eval (aig : AIG BVBit) (pred : BVPred) (assign : BVExpr.Assignment)
    : ⟦bitblast aig pred, assign.toAIGAssignment⟧
        =
      pred.eval assign := by
  cases pred with
  | bin lhs op rhs =>
    cases op with
    | eq => simp [bitblast]
    | neq => simp [bitblast]

end BVPred

namespace BVLogicalExpr

theorem bitblast.go_eval_eq_eval (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment) :
    ⟦ofBoolExprCached.go expr aig BVPred.bitblast, assign.toAIGAssignment⟧ = expr.eval assign := by
  induction expr generalizing aig with
  | const => simp [ofBoolExprCached.go]
  | literal => simp [ofBoolExprCached.go]
  | not expr ih => simp [ofBoolExprCached.go, ih]
  | gate g lhs rhs lih rih => cases g <;> simp [ofBoolExprCached.go, Gate.eval, lih, rih]

theorem eval_eq_bitblast_denote (expr : BVLogicalExpr) (assign : BVExpr.Assignment)
    : expr.eval assign
        =
      ⟦bitblast expr, assign.toAIGAssignment⟧ := by
  unfold bitblast
  unfold ofBoolExprCached
  rw [bitblast.go_eval_eq_eval]

theorem bitblast_denote_eq_eval (expr : BVLogicalExpr) (assign : BVExpr.Assignment)
    : ⟦bitblast expr, assign.toAIGAssignment⟧
        =
      expr.eval assign := by
  unfold bitblast
  unfold ofBoolExprCached
  rw [bitblast.go_eval_eq_eval]

theorem unsat_of_bitblast (expr : BVLogicalExpr)
    : expr.bitblast.unsat → expr.unsat :=  by
  intro h assign
  rw [← bitblast_denote_eq_eval]
  apply h

end BVLogicalExpr
