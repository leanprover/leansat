import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_144 :
 ∀ (X C1 C2 : BitVec 64), (X ||| C1) &&& C2 = (X ||| C1 &&& C2) &&& C2
:= by intros; bv_decide
