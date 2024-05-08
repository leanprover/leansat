import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_135 :
 ∀ (X C1 C2 : BitVec 64), (X ^^^ C1) &&& C2 = X &&& C2 ^^^ C1 &&& C2
:= by intros; bv_decide
