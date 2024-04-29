import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_891 :
 ∀ (x N : BitVec 13), udiv? x (1 <<< N) ⊑ some (x >>> N)
:= by bv_decide
