import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_698 :
 ∀ (a b d : BitVec 64), ofBool (a &&& b == 0) &&& ofBool (a &&& d == 0) = ofBool (a &&& (b ||| d) == 0)
:= by bv_decide