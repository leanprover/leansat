import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_887_2 :
 ∀ (a C1 : BitVec 64), ofBool (a == C1) &&& ofBool (a != C1) = ofBool false
:= by bv_decide
