import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_2284 :
 ∀ (A B : BitVec 64), A ||| (A ||| B) ^^^ -1 = A ||| B ^^^ -1
:= by bv_decide
