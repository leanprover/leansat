import LeanSAT.Reflect.BVExpr.BitBlast

open AIG

namespace BVExpr

def Assignment.toAIGAssignment (assign : Assignment) : BVBit → Bool :=
  fun bit => (assign.getD bit.var).bv.getLsb bit.idx

@[simp]
theorem Assignment.toAIGAssignment_apply (assign : Assignment) (bit : BVBit)
    : assign.toAIGAssignment bit = (assign.getD bit.var).bv.getLsb bit.idx := by
  rfl

-- TODO: denotational theory for blastVar
-- TODO: denotational theory for blastConst

-- TODO: replace these two with theory that every bit in the stream returned by bitblast corresponds
-- to a getLsb from the target

@[simp]
theorem bitblast_denote_eq_eval_getLsb (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦(expr.bitblast aig).1.1, (expr.bitblast aig).2.getRef idx hidx, assign.toAIGAssignment⟧
          =
        (expr.eval assign).getLsb idx
    := by
  intro idx hidx
  induction expr generalizing aig with
  | const =>
    simp [bitblast]
    -- TODO: blastConst denotation
    sorry
  | var =>
    simp [bitblast, hidx]
    -- TODO: blastVar denotation
    sorry
  | bin lhs op rhs lih rih =>
    cases op with
    | and =>
      simp [bitblast, lih, rih]
      -- TODO: very easy with LawfulOperator style reasoning
      sorry
  | un op expr ih =>
    cases op with 
    | not => simp [bitblast, ih, hidx]


end BVExpr

namespace BVPred

theorem mkEq_denote_iff_eval_beq (aig : AIG BVBit) (pair : ExprPair) (assign : BVExpr.Assignment)
    : ⟦mkEq aig pair, assign.toAIGAssignment⟧
        ↔
      (pair.lhs.eval assign == pair.rhs.eval assign) := by
  rw [beq_iff_eq]
  unfold mkEq
  dsimp
  -- TODO: simp only this after we got bitblast's denotation back
  simp
  constructor
  . intro h
    apply BitVec.eq_of_getLsb_eq
    intro i
    specialize h i.val i.isLt
    -- TODO: fix this after we got bitblast's denotation back
    sorry
  . intro h idx hidx
    -- TODO: fix this after we got bitblast's denotation back
    sorry

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
