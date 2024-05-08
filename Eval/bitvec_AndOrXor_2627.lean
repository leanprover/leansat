import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_2627 :
 ∀ (a c b : BitVec 64), a ^^^ c ^^^ (a ||| b) = (a ^^^ -1) &&& b ^^^ c
:= by intros; bv_decide
