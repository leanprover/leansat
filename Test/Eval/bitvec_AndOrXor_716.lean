import Std.Tactic.BVDecide

theorem bitvec_AndOrXor_716 :
 ∀ (a b d : BitVec 64), ((a &&& b == a) && (a &&& d == a)) = (a &&& (b &&& d) == a)
:= by intros; bv_decide
