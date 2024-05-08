import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_2367 :
 ∀ (A C1 op1 : BitVec 64), A ||| C1 ||| op1 = A ||| op1 ||| C1
:= by intros; bv_decide
