import LeanSAT.Reflect.Tactics.BVDecide

open BitVec

theorem bitvec_InstCombineShift__582 :
 ∀ (X C : BitVec 64), X <<< C >>> C = X &&& (-1 : BitVec _) >>> C
:= by bv_decide
