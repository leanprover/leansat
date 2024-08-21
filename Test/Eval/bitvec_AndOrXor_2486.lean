import Std.Tactic.BVDecide

theorem bitvec_AndOrXor_2486 :
 ∀ (x C : BitVec 64), x + C ^^^ -1 = -1 - C - x
:= by intros; bv_decide
