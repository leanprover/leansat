/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Not

open AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

@[simp]
theorem blastNot_eq_eval_getLsb (aig : AIG α) (target : RefStream aig w)
    (assign : α → Bool)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (blastNot aig target).aig,
          (blastNot aig target).stream.get idx hidx,
          assign
        ⟧
          =
        !⟦
          aig,
          target.get idx hidx,
          assign
         ⟧
        := by
  intro idx hidx
  unfold blastNot
  simp

end bitblast
end BVExpr
