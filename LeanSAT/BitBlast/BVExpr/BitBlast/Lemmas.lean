/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Pred

open AIG

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
