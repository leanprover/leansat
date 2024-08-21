import Std.Tactic.BVDecide

theorem bitvec_AndOrXor_2617 :
 ∀ (a b : BitVec 64), a &&& (b ^^^ -1) ^^^ (a ^^^ -1) &&& b = a ^^^ b
:= by intros; bv_decide
