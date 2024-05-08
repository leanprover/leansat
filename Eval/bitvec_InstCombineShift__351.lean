import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_InstCombineShift__351 :
 ∀ (X C1 C2 : BitVec 7), (X * C1) <<< C2 = X * C1 <<< C2
:= by intros; bv_decide
