theorem bitvec_AddSub_1165 :
 ∀ (a b : BitVec 64), 0 - a + (0 - b) = 0 - (a + b)
:= by alive_auto
      done --ring