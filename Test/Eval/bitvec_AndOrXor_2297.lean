import LeanSAT.Tactics.BVDecide

theorem bitvec_AndOrXor_2297 :
 ∀ (A B : BitVec 64), A &&& B ||| A ^^^ -1 ^^^ B = A ^^^ -1 ^^^ B
:= by intros; bv_decide
