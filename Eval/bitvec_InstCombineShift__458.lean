-- set_option maxRecDepth 9999 in
import LeanSAT.Reflect.Tactics.BVDecide

open BitVec

theorem bitvec_InstCombineShift__458 :
 ∀ (Y X C : BitVec 31), (sshiftRight X (BitVec.toNat C) - Y) <<< C = X - Y <<< C &&& (-1 : BitVec _) <<< C
:= by bv_decide
