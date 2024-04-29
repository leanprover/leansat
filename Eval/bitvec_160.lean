theorem bitvec_160 :
 ∀ (x C1 C2 : BitVec 7), x <<< C2 * C1 = x * C1 <<< C2
:= by alive_auto
      try sorry