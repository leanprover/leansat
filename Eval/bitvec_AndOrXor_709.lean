import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_709 :
 ∀ (a b d : BitVec 64), ofBool (a &&& b == b) &&& ofBool (a &&& d == d) = ofBool (a &&& (b ||| d) == b ||| d)
:= by bv_decide
