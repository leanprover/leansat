import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AddSub_1560 :
 ∀ (a : BitVec 64), -1 - a = a ^^^ -1
:= by bv_decide
