import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AddSub_1564 :
 ∀ (x C : BitVec 64), C - (x ^^^ -1) = x + (C + 1)
:= by intros; bv_decide
