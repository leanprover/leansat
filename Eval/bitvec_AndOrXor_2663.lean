import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_2663 :
 ∀ (a b : BitVec 64), xor (a ≤ b) (a != b) = (b ≤ a)
:= by bv_decide
