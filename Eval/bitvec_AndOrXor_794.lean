import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_794 :
 ∀ (a b : BitVec 64), (BitVec.slt b a) && (a != b) = (BitVec.slt b a)
:= by intros; bv_decide
