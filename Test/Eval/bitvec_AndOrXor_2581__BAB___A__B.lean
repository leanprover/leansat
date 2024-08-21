import Std.Tactic.BVDecide

theorem bitvec_AndOrXor_2581__BAB___A__B :
 ∀ (a op1 : BitVec 64), (a ||| op1) ^^^ op1 = a &&& (op1 ^^^ -1)
:= by intros; bv_decide
