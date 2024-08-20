import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AddSub_1560 :
 ∀ (a : BitVec 64), -1 - a = a ^^^ -1
:= by intros; bv_decide
