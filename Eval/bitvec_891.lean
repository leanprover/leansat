theorem bitvec_891 :
 ∀ (x N : BitVec 13), udiv? x (1 <<< N) ⊑ some (x >>> N)
:= by alive_auto
      try sorry