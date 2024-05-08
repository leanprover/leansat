import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_152 :
 ∀ (x : BitVec 64), x * -1 = 0 - x
:= by intros; bv_decide
