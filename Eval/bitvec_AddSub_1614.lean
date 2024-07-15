import LeanSAT.Tactics.BVDecide

theorem bitvec_AddSub_1614 :
 ∀ (Y X : BitVec 64), X - (X + Y) = 0 - Y
:= by intros; bv_decide
