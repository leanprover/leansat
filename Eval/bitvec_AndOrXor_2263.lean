import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_2263 :
 ∀ (B op0 : BitVec 64), op0 ||| op0 ^^^ B = op0 ||| B
:= by intros; bv_decide
