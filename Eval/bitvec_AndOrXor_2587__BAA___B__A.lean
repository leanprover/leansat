import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_2587__BAA___B__A :
 ∀ (a op1 : BitVec 64), a &&& op1 ^^^ op1 = (a ^^^ -1) &&& op1
:= by intros; bv_decide
