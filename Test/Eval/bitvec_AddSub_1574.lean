import Std.Tactic.BVDecide

theorem bitvec_AddSub_1574 :
 ∀ (X C C2 : BitVec 64), C - (X + C2) = C - C2 - X
:= by intros; bv_decide
