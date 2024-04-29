import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_276_2 :
 ∀ (Y X : BitVec 5),
  (Option.bind (udiv? X Y) fun fst => some (fst * (0 - Y))) ⊑ Option.bind (urem? X Y) fun fst => some (fst - X)
:= by bv_decide
