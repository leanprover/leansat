import LeanSAT.Frontend.BVDecide

theorem bitvec_AddSub_1619 :
 ∀ (Y X : BitVec 64), X - Y - X = 0 - Y
:= by intros; bv_decide
