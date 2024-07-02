/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.AIG.Basic
import LeanSAT.Reflect.BVExpr.Basic

namespace BVExpr

def Assignment.toAIGAssignment (assign : Assignment) : BVBit → Bool :=
  fun bit => (assign.getD bit.var).bv.getLsb bit.idx

@[simp]
theorem Assignment.toAIGAssignment_apply (assign : Assignment) (bit : BVBit)
    : assign.toAIGAssignment bit = (assign.getD bit.var).bv.getLsb bit.idx := by
  rfl

end BVExpr
