import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_InstCombineShift__582 :
 ∀ (X C : BitVec 64), X <<< C >>> C = X &&& (-1) >>> C
:= by bv_decide
