import Std.Tactic.BVDecide

theorem bitvec_AndOrXor_2265 :
 ∀ (A B : BitVec 64), A &&& B ||| A ^^^ B = A ||| B
:= by intros; bv_decide
