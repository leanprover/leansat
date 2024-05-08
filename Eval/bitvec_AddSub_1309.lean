import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AddSub_1309 :
 ∀ (a b : BitVec 64), (a &&& b) + (a ||| b) = a + b
:= by intros; bv_decide
