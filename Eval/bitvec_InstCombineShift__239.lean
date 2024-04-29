theorem bitvec_InstCombineShift__239 :
 ∀ (X C : BitVec 64), X <<< C >>> C = X &&& (-1) >>> C
:= by alive_auto
      try sorry