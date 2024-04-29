import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_794 :
 ∀ (a b : BitVec 64), (a >ₛ b) &&& ofBool (a != b) = (a >ₛ b)
:= by bv_decide
