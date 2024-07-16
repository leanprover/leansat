import LeanSAT.Tactics.BVDecide

theorem bitvec_AndOrXor_2430 :
 ∀ (y x : BitVec 64), (x ||| y) ^^^ -1 = (x ^^^ -1) &&& (y ^^^ -1)
:= by intros; bv_decide
