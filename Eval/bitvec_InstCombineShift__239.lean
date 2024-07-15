import LeanSAT.Tactics.BVDecide

theorem bitvec_InstCombineShift__239 :
 ∀ (X C : BitVec 64), X <<< C >>> C = X &&& (-1 : BitVec _) >>> C
:= by intros; bv_decide
