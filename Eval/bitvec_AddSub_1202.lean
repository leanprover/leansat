theorem bitvec_AddSub_1202 :
 ∀ (x C : BitVec 64), (x ^^^ -1) + C = C - 1 - x
:= by alive_auto
      try sorry