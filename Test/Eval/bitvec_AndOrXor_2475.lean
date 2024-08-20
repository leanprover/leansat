import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AndOrXor_2475 :
 ∀ (x C : BitVec 64), C - x ^^^ -1 = x + (-1 - C)
:= by intros; bv_decide
