import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AddSub_1564 :
 ∀ (x C : BitVec 64), C - (x ^^^ -1) = x + (C + 1)
:= by bv_decide
