-- set_option maxRecDepth 9999 in
import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_InstCombineShift__458 :
 ∀ (Y X C : BitVec 31), (sshr X (BitVec.toNat C) - Y) <<< C = X - Y <<< C &&& (-1) <<< C
:= by -- bv_decide -- TIMES OUT WITH MAX RECURSION DEPTH
      try sorry
