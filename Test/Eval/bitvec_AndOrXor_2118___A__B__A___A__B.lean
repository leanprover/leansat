import Std.Tactic.BVDecide

theorem bitvec_AndOrXor_2118___A__B__A___A__B :
 ∀ (A B : BitVec 64), A &&& B ||| A ^^^ -1 = A ^^^ -1 ||| B
:= by intros; bv_decide
