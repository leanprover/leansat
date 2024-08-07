/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.RotateLeft

open AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastRotateLeft

theorem go_get_aux (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx : idx < curr),
        (go input distance curr hcurr s).get idx (by omega)
          =
        s.get idx hidx := by
  intro idx hidx
  unfold go
  split
  . dsimp
    split
    . rw [go_get_aux]
      rw [AIG.RefStream.get_push_ref_lt]
    . rw [go_get_aux]
      rw [AIG.RefStream.get_push_ref_lt]
  . dsimp
    simp only [RefStream.get, Ref.mk.injEq]
    have : curr = w := by omega
    subst this
    simp
termination_by w - curr

theorem go_get (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx1 : idx < w),
        curr ≤ idx
          →
        (go input distance curr hcurr s).get idx hidx1
          =
        if hidx3:idx < distance % w then
          input.get (w - (distance % w) + idx) (by omega)
        else
          input.get (idx - (distance % w)) (by omega)
        := by
  intro idx hidx1 hidx2
  unfold go
  split
  . dsimp
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      split
      . split
        . rw [go_get_aux]
          rw [AIG.RefStream.get_push_ref_eq']
          . simp [heq]
          . omega
        . omega
      . split
        . omega
        . rw [go_get_aux]
          rw [AIG.RefStream.get_push_ref_eq']
          . simp [heq]
          . omega
    | inr heq =>
      split
      . rw [go_get]
        omega
      . rw [go_get]
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
        (blastRotateLeft aig target).stream.get idx hidx,
        assign
      ⟧
        =
      if hidx2:idx < target.distance % w then
        ⟦aig, target.stream.get (w - (target.distance % w) + idx) (by omega), assign⟧
      else
        ⟦aig, target.stream.get (idx - (target.distance % w)) (by omega), assign⟧
      := by
  intros
  unfold blastRotateLeft
  dsimp
  rw [blastRotateLeft.go_get]
  . split
    . rfl
    . rfl
  . omega

end bitblast
end BVExpr
