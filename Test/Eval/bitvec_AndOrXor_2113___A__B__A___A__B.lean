import LeanSAT.Tactics.BVDecide

theorem bitvec_AndOrXor_2113___A__B__A___A__B :
 ∀ (A B : BitVec 64), (A ^^^ -1) &&& B ||| A = A ||| B
:= by intros; bv_decide
