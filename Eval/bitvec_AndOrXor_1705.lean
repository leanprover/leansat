import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_1705 :
 ∀ (A B : BitVec 64), ofBool (B == 0) ||| (B >ᵤ A) = (B + -1 ≥ᵤ A)
:= by bv_decide
