theorem bitvec_InstCombineShift__497''' :
 ∀ (X C C2 : BitVec 64), (X + C2) <<< C = X <<< C + C2 <<< C
:= by alive_auto
      try sorry