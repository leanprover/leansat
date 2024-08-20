import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

theorem bitvec_239 :
 ∀ (Y X : BitVec 8), (0 - X) * (0 - Y) = X * Y
:= by intros; bv_decide
