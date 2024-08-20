import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AddSub_1164 :
 ∀ (a b : BitVec 64), 0 - a + b = b - a
:= by intros; bv_decide
