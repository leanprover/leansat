import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_716 :
 ∀ (a b d : BitVec 64), (a &&& b == a) && (a &&& d == a) = (a &&& (b &&& d) == a)
:= by bv_decide
