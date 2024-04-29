theorem bitvec_AddSub_1564 :
 ∀ (x C : BitVec 64), C - (x ^^^ -1) = x + (C + 1)
:= by alive_auto
      try sorry