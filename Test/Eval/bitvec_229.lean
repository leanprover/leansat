import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_229 :
 ∀ (X C1 Op1 : BitVec 4), (X + C1) * Op1 = X * Op1 + C1 * Op1
:= by intros; bv_decide
