import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_283 :
 ∀ (Y X : BitVec 1), X * Y = X &&& Y
:= by intros; bv_decide
