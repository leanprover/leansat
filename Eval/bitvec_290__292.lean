import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_290__292 :
 ∀ (Y Op1 : BitVec 64), 1 <<< Y * Op1 = Op1 <<< Y
:= by bv_decide
