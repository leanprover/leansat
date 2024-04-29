import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_2486 :
 ∀ (x C : BitVec 64), x + C ^^^ -1 = -1 - C - x
:= by bv_decide
