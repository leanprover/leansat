theorem bitvec_AndOrXor_2475 :
 ∀ (x C : BitVec 64), C - x ^^^ -1 = x + (-1 - C)
:= by alive_auto
      try sorry