import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_AndOrXor_2285 :
 ∀ (A B : BitVec 64), A ||| A ^^^ B ^^^ -1 = A ||| B ^^^ -1
:= by intros; bv_decide
