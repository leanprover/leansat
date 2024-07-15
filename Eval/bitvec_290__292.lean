import LeanSAT.Tactics.BVDecide
open BitVec

theorem bitvec_290__292 :
 ∀ (Y Op1 : BitVec 8), 1#8 <<< Y * Op1 = Op1 <<< Y
:= by intros; bv_decide
