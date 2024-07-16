import LeanSAT.Tactics.BVDecide

open BitVec

theorem bitvec_AndOrXor_1683_1 :
 ∀ (a b : BitVec 64), ((b < a) || (a == b)) = (b ≤ a)
:= by intros; bv_decide
