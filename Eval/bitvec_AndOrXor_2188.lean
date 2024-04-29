import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_2188 :
 ∀ (A D : BitVec 64), A &&& (D ^^^ -1) ||| (A ^^^ -1) &&& D = A ^^^ D
:= by bv_decide
