theorem bitvec_AddSub_1539 :
 ∀ (a x : BitVec 64), x - (0 - a) = x + a
:= by alive_auto
      done --ring