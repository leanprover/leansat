import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AddSub_1614 :
 ∀ (Y X : BitVec 64), X - (X + Y) = 0 - Y
:= by bv_decide
