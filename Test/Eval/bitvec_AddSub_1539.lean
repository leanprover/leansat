import LeanSAT.Frontend.BVDecide

theorem bitvec_AddSub_1539 :
 ∀ (a x : BitVec 64), x - (0 - a) = x + a
:= by intros; bv_decide
