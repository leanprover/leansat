import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AddSub_1556 :
 ∀ (y x : BitVec 1), x - y = x ^^^ y
:= by intros; bv_decide
