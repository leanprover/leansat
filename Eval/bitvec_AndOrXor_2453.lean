import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_2453 :
 ∀ (y x : BitVec 64), (x <ₛ y) ^^^ -1 = ofBool (x ≥ₛ y)
:= by bv_decide
