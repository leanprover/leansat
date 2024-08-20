import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AndOrXor_2231__A__B__B__C__A___A__B__C :
 ∀ (A C B : BitVec 64), A ^^^ B ||| B ^^^ C ^^^ A = A ^^^ B ||| C
:= by intros; bv_decide
