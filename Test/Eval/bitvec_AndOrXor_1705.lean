import LeanSAT.Tactics.BVDecide

theorem bitvec_AndOrXor_1705 :
∀ (A B : BitVec 64), ((B == 0) || (A < B)) = (A ≤ B + -1)
:= by intros; bv_decide
