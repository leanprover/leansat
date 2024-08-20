import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_InstCombineShift__239 :
 ∀ (X C : BitVec 32), X <<< C >>> C = X &&& (-1 : BitVec _) >>> C
:= by intros; bv_decide
