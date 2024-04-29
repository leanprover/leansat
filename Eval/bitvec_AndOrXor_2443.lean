import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_2443 :
 ∀ (y x : BitVec 64), sshr (x ^^^ -1) (BitVec.toNat y) ^^^ -1 = sshr x (BitVec.toNat y)
:= by bv_decide
