import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_InstCombineShift__422_1 :
 ∀ (Y X C : BitVec 31), (Y + X >>> C) <<< C = Y <<< C + X &&& (-1 : BitVec _) <<< C
:= by intros; bv_decide
