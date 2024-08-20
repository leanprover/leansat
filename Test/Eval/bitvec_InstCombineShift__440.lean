import LeanSAT.Frontend.BVDecide

theorem bitvec_InstCombineShift__440 :
 ∀ (Y X C C2 : BitVec 32), (Y ^^^ X >>> C &&& C2) <<< C = X &&& C2 <<< C ^^^ Y <<< C
:= by intros; bv_decide
