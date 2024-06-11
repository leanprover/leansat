import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Append

open AIG

namespace BVExpr
namespace bitblast

variable [BEq α] [Hashable α] [DecidableEq α]

@[simp]
theorem blastAppend_eq_eval_getLsb (aig : AIG α) (target : AppendTarget aig newWidth)
  (assign : α → Bool)
  : ∀ (idx : Nat) (hidx : idx < newWidth),
      ⟦
        (blastAppend aig target).aig,
        (blastAppend aig target).stream.getRef idx hidx,
        assign
      ⟧
        =
      if hr:idx < target.rw then
         ⟦aig, target.rhs.getRef idx hr, assign⟧
      else
         have := target.h
         ⟦aig, target.lhs.getRef (idx - target.rw) (by omega), assign⟧
    := by
  intros
  unfold blastAppend
  rcases target with ⟨lw, rw, lhs, rhs, ht⟩
  dsimp
  rw [AIG.RefStream.getRef_append]
  split <;> rfl


end bitblast
end BVExpr
