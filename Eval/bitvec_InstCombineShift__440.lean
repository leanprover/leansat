theorem bitvec_InstCombineShift__440 :
 ∀ (Y X C C2 : BitVec 64), (Y ^^^ X >>> C &&& C2) <<< C = X &&& C2 <<< C ^^^ Y <<< C
:= by alive_auto
      try sorry