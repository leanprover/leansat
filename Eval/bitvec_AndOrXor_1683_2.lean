import LeanSAT.Tactics.BVDecide

theorem bitvec_AndOrXor_1683_2 :
 ∀ (a b : BitVec 64), (b ≤ a) || (a != b) = true
:= by intros; bv_decide
