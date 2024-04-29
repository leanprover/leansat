import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_275 :
 ∀ (Y X : BitVec 5),
  (Option.bind (udiv? X Y) fun fst => some (fst * Y)) ⊑ Option.bind (urem? X Y) fun snd => some (X - snd)
:= by bv_decide
