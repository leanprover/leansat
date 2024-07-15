import LeanSAT.Tactics.BVDecide

theorem bitvec_AndOrXor_2188 :
 ∀ (A D : BitVec 64), A &&& (D ^^^ -1) ||| (A ^^^ -1) &&& D = A ^^^ D
:= by intros; bv_decide
