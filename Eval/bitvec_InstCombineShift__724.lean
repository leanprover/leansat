import LeanSAT.Tactics.BVDecide

theorem bitvec_InstCombineShift__724 :
 ∀ (A C2 C1 : BitVec 31), C1 <<< A <<< C2 = C1 <<< C2 <<< A
:= by intros; bv_decide
