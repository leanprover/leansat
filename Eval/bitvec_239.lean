import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_239 :
 ∀ (Y X : BitVec 64), (0 - X) * (0 - Y) = X * Y
:= by intros; bv_decide
