import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AndOrXor_2063__X__C1__C2____X__C2__C1__C2 :
 ∀ (x C1 C : BitVec 64), x ^^^ C1 ||| C = (x ||| C) ^^^ C1 &&& ~~~C
:= by intros; bv_decide
