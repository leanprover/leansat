import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AddSub_1176 :
 ∀ (a b : BitVec 64), a + (0 - b) = a - b
:= by bv_decide
