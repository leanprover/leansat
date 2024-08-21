import Std.Tactic.BVDecide

theorem bitvec_AndOrXor_887_2 :
 ∀ (a C1 : BitVec 64), ((a == C1) && (a != C1)) = false
:= by intros; bv_decide
