import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AddSub_1202 :
 ∀ (x C : BitVec 64), (x ^^^ -1) + C = C - 1 - x
:= by intros; bv_decide
