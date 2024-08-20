import LeanSAT.Frontend.BVDecide

theorem bitvec_AndOrXor_709 :
 ∀ (a b d : BitVec 64), ((a &&& b == b) && (a &&& d == d)) = (a &&& (b ||| d) == b ||| d)
:= by intros; bv_decide
