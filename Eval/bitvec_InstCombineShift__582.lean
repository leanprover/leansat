import LeanSAT.Tactics.BVDecide

open BitVec

theorem bitvec_InstCombineShift__582 :
 ∀ (X C : BitVec 64), X <<< C >>> C = X &&& (-1 : BitVec _) >>> C
:= by intros; bv_decide
