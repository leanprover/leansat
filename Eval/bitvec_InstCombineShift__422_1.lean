theorem bitvec_InstCombineShift__422_1 :
 ∀ (Y X C : BitVec 31), (Y + X >>> C) <<< C = Y <<< C + X &&& (-1) <<< C
:= by alive_auto
      try sorry