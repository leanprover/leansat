import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_160 :
 ∀ (x C1 C2 : BitVec 7), x <<< C2 * C1 = x * C1 <<< C2
:= by intros; bv_decide
