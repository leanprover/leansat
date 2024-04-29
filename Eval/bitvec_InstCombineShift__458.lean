-- set_option maxRecDepth 9999 in
theorem bitvec_InstCombineShift__458 :
 ∀ (Y X C : BitVec 31), (sshr X (BitVec.toNat C) - Y) <<< C = X - Y <<< C &&& (-1) <<< C
:= by -- alive_auto -- TIMES OUT WITH MAX RECURSION DEPTH
      try sorry