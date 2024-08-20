import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AddSub_1165 :
 ∀ (a b : BitVec 64), 0 - a + (0 - b) = 0 - (a + b)
:= by intros; bv_decide
