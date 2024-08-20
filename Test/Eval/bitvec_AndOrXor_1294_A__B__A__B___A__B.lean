import LeanSAT.Frontend.BVDecide

theorem bitvec_AndOrXor_1294_A__B__A__B___A__B :
 ∀ (A B : BitVec 64), (A ||| B) &&& (A ^^^ -1 ^^^ B) = A &&& B
:= by intros; bv_decide
