import Std.Tactic.BVDecide

theorem bitvec_AndOrXor_2417 :
 ∀ (nx y : BitVec 64), (nx ^^^ -1 ||| y) ^^^ -1 = nx &&& (y ^^^ -1)
:= by intros; bv_decide
