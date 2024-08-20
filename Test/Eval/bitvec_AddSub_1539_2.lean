import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AddSub_1539_2 :
 ∀ (x C : BitVec 64), x - C = x + -C
:= by intros; bv_decide
