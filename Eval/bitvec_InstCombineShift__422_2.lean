-- set_option maxRecDepth 9999 in
theorem bitvec_InstCombineShift__422_2 :
 ∀ (Y X C : BitVec 31), (Y + sshr X (BitVec.toNat C)) <<< C = Y <<< C + X &&& (-1) <<< C
:= by -- alive_auto -- TIMES OUT WITH MAX RECURSION DEPTH
  try sorry