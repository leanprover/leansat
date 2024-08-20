import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

open BitVec

theorem bitvec_InstCombineShift__582 :
 ∀ (X C : BitVec 32), X <<< C >>> C = X &&& (-1 : BitVec _) >>> C
:= by intros; bv_decide
