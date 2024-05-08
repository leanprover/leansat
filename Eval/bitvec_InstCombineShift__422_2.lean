-- set_option maxRecDepth 9999 in
import LeanSAT.Reflect.Tactics.BVDecide

open BitVec

theorem bitvec_InstCombineShift__422_2 :
 ∀ (Y X C : BitVec 31), (Y + sshiftRight X (BitVec.toNat C)) <<< C = Y <<< C + X &&& (-1 : BitVec _) <<< C
:= by intros; bv_decide

