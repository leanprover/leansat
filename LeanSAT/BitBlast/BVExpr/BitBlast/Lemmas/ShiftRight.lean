/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.ShiftRight
import LeanSAT.Tactics.Normalize.BitVec

open AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

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
theorem blastShiftRightConst_eq_eval_getLsb (aig : AIG α) (target : ShiftTarget aig w)
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

opaque ushiftRight_rec (x : BitVec w₁) (y : BitVec w₂) (n : Nat) : BitVec w₁

@[simp]
theorem ushiftRight_rec_zero (x : BitVec w₁) (y : BitVec w₂) :
    ushiftRight_rec x y 0 = x >>> (y &&& BitVec.twoPow w₂ 0)  := by
  sorry

@[simp]
theorem ushiftRight_rec_succ (x : BitVec w₁) (y : BitVec w₂) :
    ushiftRight_rec x y (n + 1) =
      (ushiftRight_rec x y n) >>> (y &&& BitVec.twoPow w₂ (n + 1)) := by
  sorry

theorem shiftRight_eq_shiftRight_rec (x : BitVec ℘) (y : BitVec w₂) :
    x >>> y = ushiftRight_rec x y (w₂ - 1) := by
  sorry

theorem getLsb_shiftRight' (x : BitVec w) (y : BitVec w₂) (i : Nat) :
    (x >>> y).getLsb i = x.getLsb (y.toNat + i) := by
  sorry

namespace blastShiftRight

theorem twoPowShift_eq (aig : AIG α) (target : TwoPowShiftTarget aig w) (lhs : BitVec w)
    (rhs : BitVec target.n) (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, target.lhs.getRef idx hidx, assign⟧ = lhs.getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < target.n), ⟦aig, target.rhs.getRef idx hidx, assign⟧ = rhs.getLsb idx)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (twoPowShift aig target).aig,
          (twoPowShift aig target).stream.getRef idx hidx,
          assign
        ⟧
          =
        (lhs >>> (rhs &&& BitVec.twoPow target.n target.pow)).getLsb idx := by
  intro idx hidx
  generalize hg : twoPowShift aig target = res
  rcases target with ⟨n, lstream, rstream, pow⟩
  simp only [BitVec.and_twoPow_eq]
  unfold twoPowShift at hg
  dsimp at hg
  split at hg
  . split
    . next hif1 =>
      rw [← hg]
      simp only [RefStream.denote_ite, RefStream.getRef_cast, Ref_cast',
        blastShiftRightConst_eq_eval_getLsb]
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftRightConst)]
      rw [hright]
      simp only [hif1, ↓reduceIte]
      split
      . next hif2 =>
        rw [hleft]
        simp [getLsb_shiftRight']
      . simp only [getLsb_shiftRight', BitVec.toNat_twoPow, Bool.false_eq]
        apply BitVec.getLsb_ge
        omega
    . next hif1 =>
      simp only [Bool.not_eq_true] at hif1
      rw [← hg]
      simp only [RefStream.denote_ite, RefStream.getRef_cast, Ref_cast',
        blastShiftRightConst_eq_eval_getLsb]
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftRightConst)]
      rw [hright]
      simp only [hif1, Bool.false_eq_true, ↓reduceIte]
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftRightConst)]
      rw [hleft]
      simp only [BVDecide.Normalize.BitVec.shiftRight_zero]
  . have : rhs.getLsb pow = false := by
      apply BitVec.getLsb_ge
      dsimp
      omega
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    rw [← hg]
    rw [hleft]
    simp only [BVDecide.Normalize.BitVec.shiftRight_zero]

theorem go_eq_eval_getLsb (aig : AIG α) (distance : AIG.RefStream aig n) (curr : Nat)
      (hcurr : curr ≤ n - 1) (acc : AIG.RefStream aig w)
    (lhs : BitVec w) (rhs : BitVec n) (assign : α → Bool)
    (hacc : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, acc.getRef idx hidx, assign⟧ = (ushiftRight_rec lhs rhs curr).getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < n), ⟦aig, distance.getRef idx hidx, assign⟧ = rhs.getLsb idx)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig distance curr hcurr acc).aig,
          (go aig distance curr hcurr acc).stream.getRef idx hidx,
          assign
        ⟧
          =
        (ushiftRight_rec lhs rhs (n - 1)).getLsb idx := by
  intro idx hidx
  generalize hgo : go aig distance curr hcurr acc = res
  unfold go at hgo
  dsimp at hgo
  split at hgo
  . rw [← hgo]
    rw [go_eq_eval_getLsb]
    . intro idx hidx
      simp only [ushiftRight_rec_succ]
      rw [twoPowShift_eq (lhs := ushiftRight_rec lhs rhs curr)]
      . simp [hacc]
      . simp [hright]
    . intro idx hidx
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := twoPowShift)]
      . simp [hright]
      . simp [Ref.hgate]
  . have : curr = n - 1 := by omega
    rw [← hgo]
    simp [hacc, this]
termination_by n - 1 - curr

end blastShiftRight

theorem blastShiftRight_eq_eval_getLsb (aig : AIG α) (target : ArbitraryShiftTarget aig w0)
    (lhs : BitVec w0) (rhs : BitVec target.n) (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w0), ⟦aig, target.target.getRef idx hidx, assign⟧ = lhs.getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < target.n), ⟦aig, target.distance.getRef idx hidx, assign⟧ = rhs.getLsb idx)
    : ∀ (idx : Nat) (hidx : idx < w0),
        ⟦
          (blastShiftRight aig target).aig,
          (blastShiftRight aig target).stream.getRef idx hidx,
          assign
        ⟧
          =
        (lhs >>> rhs).getLsb idx := by
  intro idx hidx
  rw [shiftRight_eq_shiftRight_rec]
  generalize hres : blastShiftRight aig target = res
  rcases target with ⟨n, target, distance⟩
  unfold blastShiftRight at hres
  dsimp at hres
  split at hres
  . next hzero =>
    dsimp
    subst hzero
    rw [← hres]
    simp [hleft, BitVec.and_twoPow_eq]
  . rw [← hres]
    rw [blastShiftRight.go_eq_eval_getLsb]
    . intro idx hidx
      simp only [ushiftRight_rec_zero]
      rw [blastShiftRight.twoPowShift_eq]
      . simp [hleft]
      . simp [hright]
    . intros
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftRight.twoPowShift)]
      . simp [hright]
      . simp [Ref.hgate]

end bitblast
end BVExpr
