/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.ShiftRight

open AIG

namespace BVExpr
namespace bitblast

variable [BEq α] [Hashable α] [DecidableEq α]

namespace blastShiftRightConst

theorem go_getRef_aux (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig input distance curr hcurr s).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig input distance curr hcurr s = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    split at hgo
    . rw [← hgo]
      intros
      rw [go_getRef_aux]
      rw [AIG.RefStream.getRef_push_ref_lt]
    . rw [← hgo]
      intros
      rw [go_getRef_aux]
      rw [AIG.RefStream.getRef_push_ref_lt]
      . simp only [Ref.cast, Ref.mk.injEq]
        rw [AIG.RefStream.getRef_cast]
        . simp
        . assumption
      . apply go_le_size
  . dsimp at hgo
    rw [← hgo]
    simp only [Nat.le_refl, RefStream.getRef, Ref_cast', Ref.mk.injEq, true_implies]
    have : curr = w := by omega
    subst this
    simp
termination_by w - curr

theorem go_getRef (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx : idx < curr),
        (go aig input distance curr hcurr s).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_getRef_aux

theorem go_denote_mem_prefix (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr) (start : Nat) (hstart)
  : ⟦
      (go aig input distance curr hcurr s).aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply go_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign⟧ := by
  apply denote.eq_of_aig_eq (entry := ⟨aig, start,hstart⟩)
  apply IsPrefix.of
  . intros
    apply go_decl_eq
  . intros
    apply go_le_size

theorem go_eq_eval_getLsb (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
    (assign : α → Bool) (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx1 : idx < w),
        curr ≤ idx
          →
        ⟦
          (go aig input distance curr hcurr s).aig,
          (go aig input distance curr hcurr s).stream.getRef idx hidx1,
          assign
        ⟧
          =
        if hidx:(distance + idx) < w then
          ⟦aig, input.getRef (distance + idx) (by omega), assign⟧
        else
          false
        := by
  intro idx hidx1 hidx2
  generalize hgo : go aig input distance curr hcurr s = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      split at hgo
      . split
        . rw [← hgo]
          rw [go_getRef]
          rw [AIG.RefStream.getRef_push_ref_eq']
          . rw [go_denote_mem_prefix]
            . simp [heq]
            . simp [Ref.hgate]
          . rw [heq]
        . omega
      . split
        . omega
        . rw [← hgo]
          rw [go_getRef]
          rw [AIG.RefStream.getRef_push_ref_eq']
          . rw [go_denote_mem_prefix]
            . simp
            . simp [Ref.hgate]
          . rw [heq]
    | inr =>
      split at hgo
      . split
        all_goals
          next hidx =>
            rw [← hgo]
            rw [go_eq_eval_getLsb]
            . simp [hidx]
            . omega
      . split
        . omega
        . next hidx =>
          rw [← hgo]
          rw [go_eq_eval_getLsb]
          . simp [hidx]
          . omega
  . omega
termination_by w - curr

end blastShiftRightConst

@[simp]
theorem blastShiftRight_eq_eval_getLsb (aig : AIG α) (target : ShiftTarget aig w)
    (assign : α → Bool)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (blastShiftRightConst aig target).aig,
          (blastShiftRightConst aig target).stream.getRef idx hidx,
          assign
        ⟧
          =
        if hidx:(target.distance + idx) < w then
          ⟦aig, target.stream.getRef (target.distance + idx) (by omega), assign⟧
        else
          false
        := by
  intros
  unfold blastShiftRightConst
  apply blastShiftRightConst.go_eq_eval_getLsb
  omega

namespace blastArithShiftRightConst

theorem go_getRef (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx : idx < curr),
        (go input distance curr hcurr s).getRef idx (by omega)
          =
        s.getRef idx hidx := by
  intro idx hidx
  unfold go
  split
  . split
    all_goals
      rw [go_getRef]
      rw [AIG.RefStream.getRef_push_ref_lt]
  . simp only [RefStream.getRef, Ref.mk.injEq]
    have : curr = w := by omega
    subst this
    simp

theorem go_eq_eval_getLsb (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
    (assign : α → Bool) (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx1 : idx < w),
        curr ≤ idx
          →
        ⟦
          aig,
          (go input distance curr hcurr s).getRef idx hidx1,
          assign
        ⟧
          =
        if hidx:(distance + idx) < w then
          ⟦aig, input.getRef (distance + idx) (by omega), assign⟧
        else
          ⟦aig, input.getRef (w - 1) (by omega), assign⟧
        := by
  intro idx hidx1 hidx2
  generalize hgo : go input distance curr hcurr s = res
  unfold go at hgo
  split at hgo
  . cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      split at hgo
      . next hlt =>
        rw [heq] at hlt
        simp only [hlt, ↓reduceDIte]
        dsimp at hgo
        rw [← hgo]
        rw [go_getRef]
        rw [AIG.RefStream.getRef_push_ref_eq']
        . simp [heq]
        . omega
      . next hlt =>
        rw [heq] at hlt
        simp only [hlt, ↓reduceDIte]
        dsimp at hgo
        rw [← hgo]
        rw [go_getRef]
        rw [AIG.RefStream.getRef_push_ref_eq']
        . simp [heq]
    | inr =>
      split at hgo
      all_goals
        split
        all_goals
          next hidx =>
            rw [← hgo]
            rw [go_eq_eval_getLsb]
            . simp [hidx]
            . omega
  . omega

end blastArithShiftRightConst

@[simp]
theorem blastArithShiftRightConst_eq_eval_getLsb (aig : AIG α) (target : ShiftTarget aig w)
    (assign : α → Bool)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (blastArithShiftRightConst aig target).aig,
          (blastArithShiftRightConst aig target).stream.getRef idx hidx,
          assign
        ⟧
          =
        if hidx:(target.distance + idx) < w then
          ⟦aig, target.stream.getRef (target.distance + idx) (by omega), assign⟧
        else
          ⟦aig, target.stream.getRef (w - 1) (by omega), assign⟧
        := by
  intros
  unfold blastArithShiftRightConst
  rw [blastArithShiftRightConst.go_eq_eval_getLsb]
  omega

end bitblast
end BVExpr
