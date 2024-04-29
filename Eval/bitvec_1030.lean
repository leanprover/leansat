import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_1030 :
 ∀ (X : BitVec 64), sdiv? X (-1) ⊑ some (0 - X)
:= by bv_decide
