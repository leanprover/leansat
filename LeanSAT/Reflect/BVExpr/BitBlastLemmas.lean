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

theorem blastConst_eq_eval_getLsb (aig : AIG BVBit) (c : BitVec w) (assign : Assignment)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastConst aig c).aig, (blastConst aig c).stream.getRef idx hidx, assign.toAIGAssignment⟧
          =
        ((BVExpr.const c).eval assign).getLsb idx := by
  sorry

theorem blastVar_eq_eval_getLsb (aig : AIG BVBit) (var : BVVar w) (assign : Assignment)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastVar aig var).aig, (blastVar aig var).stream.getRef idx hidx, assign.toAIGAssignment⟧
          =
        ((BVExpr.var (w := w) var.ident).eval assign).getLsb idx := by
  sorry

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
      simp only [go_val_eq_bitblast]
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
  simp
  constructor
  . intro h
    apply BitVec.eq_of_getLsb_eq
    intro i
    specialize h i.val i.isLt
    rw [AIG.LawfulStreamOperator.denote_input_stream (f := BVExpr.bitblast)] at h
    rw [← h]
    simp
  . intro h idx hidx
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
