/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.ZeroExtend

open AIG

namespace BVExpr
namespace bitblast

variable [BEq α] [Hashable α] [DecidableEq α]

namespace blastZeroExtend

theorem go_getRef_aux (aig : AIG α) (w : Nat) (input : AIG.RefStream aig w) (newWidth curr : Nat)
    (hcurr : curr ≤ newWidth) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig w input newWidth curr hcurr s).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig w input newWidth curr hcurr s = res
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
    have : curr = newWidth := by omega
    subst this
    simp
termination_by newWidth - curr

theorem go_getRef (aig : AIG α) (w : Nat) (input : AIG.RefStream aig w) (newWidth curr : Nat)
    (hcurr : curr ≤ newWidth) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx : idx < curr),
        (go aig w input newWidth curr hcurr s).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_getRef_aux

theorem go_denote_mem_prefix (aig : AIG α) (w : Nat) (input : AIG.RefStream aig w) (newWidth curr : Nat)
    (hcurr : curr ≤ newWidth) (s : AIG.RefStream aig curr) (start : Nat) (hstart)
  : ⟦
      (go aig w input newWidth curr hcurr s).aig,
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

theorem go_eq_eval_getLsb (aig : AIG α) (w : Nat) (input : AIG.RefStream aig w) (newWidth curr : Nat)
    (hcurr : curr ≤ newWidth) (s : AIG.RefStream aig curr) (assign : α → Bool)
    : ∀ (idx : Nat) (hidx1 : idx < newWidth),
        curr ≤ idx
          →
        ⟦
          (go aig w input newWidth curr hcurr s).aig,
          (go aig w input newWidth curr hcurr s).stream.getRef idx hidx1,
          assign
        ⟧
          =
        if hidx:idx < w then
           ⟦aig, input.getRef idx hidx, assign⟧
        else
           false
    := by
  intro idx hidx1 hidx2
  generalize hgo : go aig w input newWidth curr hcurr s = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      split at hgo
      . next hsplit =>
        rw [heq] at hsplit
        simp only [hsplit, ↓reduceDIte]
        rw [← hgo]
        rw [go_getRef]
        rw [AIG.RefStream.getRef_push_ref_eq']
        . rw [go_denote_mem_prefix]
          . simp [heq]
          . simp [Ref.hgate]
        . omega
      . next hsplit =>
        rw [heq] at hsplit
        simp only [hsplit, ↓reduceDIte]
        rw [← hgo]
        rw [go_getRef]
        rw [AIG.RefStream.getRef_push_ref_eq']
        . rw [go_denote_mem_prefix]
          . simp [heq]
          . simp [Ref.hgate]
        . omega
    | inr =>
      split at hgo
      . rw [← hgo]
        rw [go_eq_eval_getLsb]
        omega
      . rw [← hgo]
        rw [go_eq_eval_getLsb]
        . split
          . omega
          . rfl
        . omega
  . omega
termination_by newWidth - curr

end blastZeroExtend

@[simp]
theorem blastZeroExtend_eq_eval_getLsb (aig : AIG α) (target : ExtendTarget aig newWidth)
  (assign : α → Bool)
  : ∀ (idx : Nat) (hidx : idx < newWidth),
      ⟦
        (blastZeroExtend aig target).aig,
        (blastZeroExtend aig target).stream.getRef idx hidx,
        assign
      ⟧
        =
      if hidx:idx < target.w then
         ⟦aig, target.stream.getRef idx hidx, assign⟧
      else
         false
    := by
  intro idx hidx
  unfold blastZeroExtend
  apply blastZeroExtend.go_eq_eval_getLsb
  omega

end bitblast
end BVExpr
