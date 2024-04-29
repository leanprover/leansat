import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AddSub_1539_2 :
 ∀ (x C : BitVec 64), x - C = x + -C
:= by bv_decide
