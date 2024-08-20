import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AndOrXor_2123___A__B__A__B___A__B :
 ∀ (A B : BitVec 64), A &&& (B ^^^ -1) ||| A ^^^ B = A ^^^ B
:= by intros; bv_decide
