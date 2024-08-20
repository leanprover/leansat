import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AndOrXor_2243__B__C__A__B___B__A__C :
 ∀ (A C B : BitVec 64), (B ||| C) &&& A ||| B = B ||| A &&& C
:= by intros; bv_decide
