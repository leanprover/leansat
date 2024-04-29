import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_716 :
 ∀ (a b d : BitVec 64), ofBool (a &&& b == a) &&& ofBool (a &&& d == a) = ofBool (a &&& (b &&& d) == a)
:= by bv_decide
