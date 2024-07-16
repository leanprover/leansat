import LeanSAT.Tactics.BVDecide

theorem bitvec_AndOrXor_1230__A__B___A__B :
 ∀ (notOp0 notOp1 : BitVec 64), (notOp0 ^^^ -1) &&& (notOp1 ^^^ -1) = (notOp0 ||| notOp1) ^^^ -1
:= by intros; bv_decide
