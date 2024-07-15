import LeanSAT.Tactics.BVDecide

theorem bitvec_AndOrXor_1247_AB__AB__AB :
 ∀ (A B : BitVec 64), (A &&& B ^^^ -1) &&& (A ||| B) = A ^^^ B
:= by intros; bv_decide
