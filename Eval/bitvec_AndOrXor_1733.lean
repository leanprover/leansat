import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_1733 :
 ∀ (A B : BitVec 64), (A != 0) ∨ (B != 0) = (A ||| B != 0)
:= by intros; bv_decide
