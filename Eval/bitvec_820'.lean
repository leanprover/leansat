import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_820' :
 ∀ (X Op1 : BitVec 9),
  (Option.bind (Option.bind (urem? X Op1) fun snd => some (X - snd)) fun fst => udiv? fst Op1) ⊑ udiv? X Op1
:= by bv_decide
