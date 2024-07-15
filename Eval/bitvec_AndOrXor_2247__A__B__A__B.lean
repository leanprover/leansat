import LeanSAT.Tactics.BVDecide

theorem bitvec_AndOrXor_2247__A__B__A__B :
 ∀ (A B : BitVec 64), A ^^^ -1 ||| B ^^^ -1 = A &&& B ^^^ -1
:= by intros; bv_decide
