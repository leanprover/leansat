import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AddSub_1043 :
 ∀ (C1 Z RHS : BitVec 64), (Z &&& C1 ^^^ C1) + 1 + RHS = RHS - (Z ||| ~~~C1)
:= by intros; bv_decide
