theorem bitvec_820 :
 ∀ (X Op1 : BitVec 9),
  (Option.bind (Option.bind (urem? X Op1) fun snd => some (X - snd)) fun fst => sdiv? fst Op1) ⊑ sdiv? X Op1
:= by alive_auto
      try sorry