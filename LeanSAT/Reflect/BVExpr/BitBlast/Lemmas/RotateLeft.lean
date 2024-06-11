import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.RotateLeft

open AIG

namespace BVExpr
namespace bitblast

variable [BEq α] [Hashable α] [DecidableEq α]

namespace blastRotateLeft

theorem go_getRef_aux (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx : idx < curr),
        (go input distance curr hcurr s).getRef idx (by omega)
          =
        s.getRef idx hidx := by
  intro idx hidx
  unfold go
  split
  . dsimp
    split
    . rw [go_getRef_aux]
      rw [AIG.RefStream.getRef_push_ref_lt]
    . rw [go_getRef_aux]
      rw [AIG.RefStream.getRef_push_ref_lt]
  . dsimp
    simp only [RefStream.getRef, Ref.mk.injEq]
    congr
    . omega
    . simp
termination_by w - curr

theorem go_getRef (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx1 : idx < w),
        curr ≤ idx
          →
        (go input distance curr hcurr s).getRef idx hidx1
          =
        if hidx3:idx < distance % w then
          input.getRef (w - (distance % w) + idx) (by omega)
        else
          input.getRef (idx - (distance % w)) (by omega)
        := by
  intro idx hidx1 hidx2
  unfold go
  split
  . dsimp
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      split
      . split
        . rw [go_getRef_aux]
          rw [AIG.RefStream.getRef_push_ref_eq']
          . simp [heq]
          . omega
        . omega
      . split
        . omega
        . rw [go_getRef_aux]
          rw [AIG.RefStream.getRef_push_ref_eq']
          . simp [heq]
          . omega
    | inr heq =>
      split
      . rw [go_getRef]
        omega
      . rw [go_getRef]
        omega
  . omega
termination_by w - curr

end blastRotateLeft

@[simp]
theorem blastRotateLeft_eq_eval_getLsb (aig : AIG α) (target : ShiftTarget aig w)
  (assign : α → Bool)
  : ∀ (idx : Nat) (hidx : idx < w),
      ⟦
        (blastRotateLeft aig target).aig,
        (blastRotateLeft aig target).stream.getRef idx hidx,
        assign
      ⟧
        =
      if hidx2:idx < target.distance % w then
        ⟦aig, target.stream.getRef (w - (target.distance % w) + idx) (by omega), assign⟧
      else
        ⟦aig, target.stream.getRef (idx - (target.distance % w)) (by omega), assign⟧
      := by
  intros
  unfold blastRotateLeft
  dsimp
  rw [blastRotateLeft.go_getRef]
  . split
    . rfl
    . rfl
  . omega

end bitblast
end BVExpr
