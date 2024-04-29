import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AddSub_1295 :
 ∀ (a b : BitVec 64), (a &&& b) + (a ^^^ b) = a ||| b
:= by bv_decide
