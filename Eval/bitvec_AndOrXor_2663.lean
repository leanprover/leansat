import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_2663 :
 ∀ (a b : BitVec 64), (a ≤ᵤ b) ^^^ ofBool (a != b) = (a ≥ᵤ b)
:= by bv_decide
