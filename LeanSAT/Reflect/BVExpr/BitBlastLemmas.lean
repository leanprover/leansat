import LeanSAT.Reflect.BVExpr.BitBlast

open AIG

namespace BVExpr

def Assignment.toAIGAssignment (assign : Assignment) : BVBit → Bool :=
  fun bit => (assign.getD bit.var).bv.getLsb bit.idx

@[simp]
theorem Assignment.toAIGAssignment_apply (assign : Assignment) (bit : BVBit)
    : assign.toAIGAssignment bit = (assign.getD bit.var).bv.getLsb bit.idx := by
  rfl

theorem bitblast.go_val_eq_bitblast (aig : AIG BVBit) (expr : BVExpr w) (idx : Nat) (hidx : idx < w)
    : (go aig expr idx hidx).val = bitblast aig ⟨expr, idx, hidx⟩ := by
  rfl

theorem bitblast.go_denote_eq_eval (aig : AIG BVBit) (expr : BVExpr w) (idx : Nat) (hidx : idx < w)
    (assign : Assignment)
    : ⟦(bitblast.go aig expr idx hidx).val, assign.toAIGAssignment⟧
        =
      (expr.eval assign).getLsb idx := by
  induction expr generalizing aig with
  | var =>
    simp [go, hidx]
  | const =>
    simp [go]
  | bin lhs op rhs lih rih =>
    cases op with
    | and =>
      simp only [go, denote_mkAndCached, Ref_cast, rih, eval_bin, BVBinOp.eval_and,
        BitVec.getLsb_and]
      simp only [bitblast.go_val_eq_bitblast (go aig lhs idx hidx).val.aig]
      rw [LawfulOperator.denote_input_entry (f := bitblast)]
      rw [lih]
  | un op expr ih =>
    cases op with
    | not =>
      simp [go, ih, hidx]

@[simp]
theorem bitblast_denote_eq_eval_getLsb (aig : AIG BVBit) (target : SingleBit) (assign : Assignment)
    : ⟦bitblast aig target, assign.toAIGAssignment⟧
        =
      (target.expr.eval assign).getLsb target.idx := by
  unfold bitblast
  rw [bitblast.go_denote_eq_eval]

@[simp]
theorem mkBitEq_denote_eq_eval_getLsb_eq (aig : AIG BVBit) (pair : BitPair) (assign : Assignment)
    : ⟦mkBitEq aig pair, assign.toAIGAssignment⟧
        =
      (
        (pair.lhs.eval assign).getLsb pair.idx
          ==
        (pair.rhs.eval assign).getLsb pair.idx
      ) := by
  unfold mkBitEq
  -- TODO: potentially more theory around BitPair
  simp [LawfulOperator.denote_input_entry (f := bitblast), BitPair.leftBit, BitPair.rightBit]

end BVExpr

namespace BVPred

theorem mkEq.go_denote_eq_eval (aig : AIG BVBit) (lhs rhs : BVExpr w) (idx : Nat) (hidx : idx ≤ w)
    (assign : BVExpr.Assignment)
    : ⟦go aig lhs rhs idx hidx, assign.toAIGAssignment⟧
        ↔
      (∀ bit < idx, (lhs.eval assign).getLsb bit = (rhs.eval assign).getLsb bit) := by
  induction idx using Nat.caseStrongInductionOn with
  | zero =>
    simp only [go, mkConstCached_eval_eq_mkConst_eval, denote_mkConst, Nat.zero_eq, true_iff]
    intro bit hbit
    contradiction
  | ind idx ih =>
    constructor
    . intro h bit hbit
      specialize ih idx (by omega) (by omega)
      simp only [go, denote_mkAndCached, Ref_ofEntrypoint, denote_projected_entry,
        BVExpr.mkBitEq_denote_eq_eval_getLsb_eq, Ref_cast, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨hl, hr⟩
      rw [LawfulOperator.denote_input_entry (f := BVExpr.mkBitEq)] at hr
      simp only [hr, true_iff] at ih
      have : bit ≤ idx := by omega
      cases Nat.eq_or_lt_of_le this with
      | inl h =>
        rw [h]
        assumption
      | inr h =>
        apply ih
        assumption
    . intro h
      simp only [go, denote_mkAndCached, Ref_ofEntrypoint, denote_projected_entry,
        BVExpr.mkBitEq_denote_eq_eval_getLsb_eq, Ref_cast, Bool.and_eq_true, beq_iff_eq]
      constructor
      . apply h
        omega
      . rw [LawfulOperator.denote_input_entry (f := BVExpr.mkBitEq)]
        rw [ih]
        . intro bit hbit
          apply h
          omega
        . omega

theorem mkEq_denote_iff_eval_beq (aig : AIG BVBit) (pair : ExprPair) (assign : BVExpr.Assignment)
    : ⟦mkEq aig pair, assign.toAIGAssignment⟧
        ↔
      (pair.lhs.eval assign == pair.rhs.eval assign) := by
  rw [beq_iff_eq]
  unfold mkEq
  rw [mkEq.go_denote_eq_eval]
  constructor
  . intro h
    apply BitVec.eq_of_getLsb_eq
    intro i
    specialize h i.val i.isLt
    assumption
  . intro h _ _
    rw [h]


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

@[simp]
theorem bitblast_denote_eq_eval (expr : BVLogicalExpr) (assign : BVExpr.Assignment)
    : ⟦bitblast expr, assign.toAIGAssignment⟧
        =
      expr.eval assign := by
  unfold bitblast
  unfold ofBoolExprCached
  rw [bitblast.go_eval_eq_eval]


end BVLogicalExpr
