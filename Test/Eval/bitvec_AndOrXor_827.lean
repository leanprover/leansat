import LeanSAT.Tactics.BVDecide

theorem bitvec_AndOrXor_827 :
 ∀ (a b : BitVec 64), ((a == 0) && (b == 0)) = (a ||| b == 0)
:= by intros; bv_decide
