import LeanSAT.Frontend.BVDecide

theorem bitvec_InstCombineShift__476 :
 ∀ (Y X C C2 : BitVec 32), (X >>> C &&& C2 ||| Y) <<< C = X &&& C2 <<< C ||| Y <<< C
:= by intros; bv_decide
