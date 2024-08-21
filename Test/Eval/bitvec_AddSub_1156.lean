import Std.Tactic.BVDecide

theorem bitvec_AddSub_1156 :
 ∀ (b : BitVec 64), b + b = b <<< 1
:= by intros; bv_decide
