import LeanSAT.Tactics.BVDecide

theorem bitvec_AndOrXor_698 :
 ∀ (a b d : BitVec 64), ((a &&& b == 0) && (a &&& d == 0)) = (a &&& (b ||| d) == 0)
:= by intros; bv_decide
