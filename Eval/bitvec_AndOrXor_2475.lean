import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_2475 :
 ∀ (x C : BitVec 64), C - x ^^^ -1 = x + (-1 - C)
:= by bv_decide
