theorem bitvec_InstCombineShift__476 :
 ∀ (Y X C C2 : BitVec 64), (X >>> C &&& C2 ||| Y) <<< C = X &&& C2 <<< C ||| Y <<< C
:= by alive_auto
      try sorry