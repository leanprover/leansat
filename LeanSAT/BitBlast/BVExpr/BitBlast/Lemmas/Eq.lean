/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Eq

open AIG

namespace BVPred

variable [Hashable α] [DecidableEq α]

theorem mkEq_denote_eq_eval_beq (aig : AIG α) (pair : AIG.BinaryRefStream aig w) (assign : α → Bool)
    (lhs rhs : BitVec w)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, pair.lhs.getRef idx hidx, assign⟧ = lhs.getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, pair.rhs.getRef idx hidx, assign⟧ = rhs.getLsb idx)
    :  ⟦mkEq aig pair, assign⟧
         =
       (lhs == rhs) := by
  unfold mkEq
  rw [Bool.eq_iff_iff]
  simp
  constructor
  . intro h
    ext
    rw [← hleft, ← hright]
    . simp [h]
    . omega
    . omega
  . intro h idx hidx
    rw [hleft, hright]
    simp [h]

end BVPred
