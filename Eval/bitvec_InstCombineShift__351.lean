theorem bitvec_InstCombineShift__351 :
 ∀ (X C1 C2 : BitVec 7), (X * C1) <<< C2 = X * C1 <<< C2
:= by alive_auto
      try sorry