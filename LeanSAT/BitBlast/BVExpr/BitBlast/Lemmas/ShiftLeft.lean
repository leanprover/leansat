/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.ShiftLeft

open AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastShiftLeftConst

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
      . simp only [Ref.cast, Ref.mk.injEq]
        rw [AIG.RefStream.getRef_cast]
        . simp
        . assumption
      . apply go_le_size
    . rw [← hgo]
      intros
      rw [go_getRef_aux]
      rw [AIG.RefStream.getRef_push_ref_lt]
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
  apply denote.eq_of_IsPrefix (entry := ⟨aig, start,hstart⟩)
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
        if hidx:idx < distance then
          false
        else
          ⟦aig, input.getRef (idx - distance) (by omega), assign⟧
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
            . simp
            . simp [Ref.hgate]
          . rw [heq]
        . omega
      . split
        . omega
        . rw [← hgo]
          rw [go_getRef]
          rw [AIG.RefStream.getRef_push_ref_eq']
          . rw [go_denote_mem_prefix]
            . simp [heq]
            . simp [Ref.hgate]
          . rw [heq]
    | inr =>
      split at hgo
      . split
        . next hidx =>
          rw [← hgo]
          rw [go_eq_eval_getLsb]
          . simp [hidx]
          . omega
        . next hidx =>
          rw [← hgo]
          rw [go_eq_eval_getLsb]
          . simp only [hidx, ↓reduceDIte, RefStream.getRef_cast, Ref_cast']
            rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
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

end blastShiftLeftConst

@[simp]
theorem blastShiftLeftConst_eq_eval_getLsb (aig : AIG α) (target : ShiftTarget aig w)
    (assign : α → Bool)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (blastShiftLeftConst aig target).aig,
          (blastShiftLeftConst aig target).stream.getRef idx hidx,
          assign
        ⟧
          =
        if hidx:idx < target.distance then
          false
        else
          ⟦aig, target.stream.getRef (idx - target.distance) (by omega), assign⟧
        := by
  intros
  unfold blastShiftLeftConst
  apply blastShiftLeftConst.go_eq_eval_getLsb
  omega

namespace blastShiftLeft

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
        (lhs <<< (rhs &&& BitVec.twoPow target.n target.pow)).getLsb idx := by
  intro idx hidx
  generalize hg : twoPowShift aig target = res
  rcases target with ⟨n, lstream, rstream, pow⟩
  simp only [BitVec.and_twoPow]
  unfold twoPowShift at hg
  dsimp at hg
  split at hg
  . split
    . next hif1 =>
      rw [← hg]
      simp only [RefStream.denote_ite, RefStream.getRef_cast, Ref_cast',
        blastShiftLeftConst_eq_eval_getLsb]
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftLeftConst)]
      rw [hright]
      simp only [hif1, ↓reduceIte]
      split
      . simp only [BitVec.shiftLeft_eq', BitVec.toNat_twoPow, BitVec.getLsb_shiftLeft,
        Bool.false_eq, Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt, and_imp]
        intros
        apply BitVec.getLsb_ge
        omega
      . next hif2 =>
        rw [hleft]
        simp only [Nat.not_lt] at hif2
        simp only [BitVec.shiftLeft_eq', BitVec.toNat_twoPow, BitVec.getLsb_shiftLeft, hidx,
          decide_True, Bool.true_and, Bool.iff_and_self, Bool.not_eq_true', decide_eq_false_iff_not,
          Nat.not_lt]
        omega
    . next hif1 =>
      simp only [Bool.not_eq_true] at hif1
      rw [← hg]
      simp only [RefStream.denote_ite, RefStream.getRef_cast, Ref_cast',
        blastShiftLeftConst_eq_eval_getLsb]
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftLeftConst)]
      rw [hright]
      simp only [hif1, Bool.false_eq_true, ↓reduceIte]
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftLeftConst)]
      rw [hleft]
      simp
  . have : rhs.getLsb pow = false := by
      apply BitVec.getLsb_ge
      dsimp
      omega
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    rw [← hg]
    rw [hleft]
    simp

theorem go_eq_eval_getLsb (aig : AIG α) (distance : AIG.RefStream aig n) (curr : Nat)
      (hcurr : curr ≤ n - 1) (acc : AIG.RefStream aig w)
    (lhs : BitVec w) (rhs : BitVec n) (assign : α → Bool)
    (hacc : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, acc.getRef idx hidx, assign⟧ = (BitVec.shiftLeftRec lhs rhs curr).getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < n), ⟦aig, distance.getRef idx hidx, assign⟧ = rhs.getLsb idx)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig distance curr hcurr acc).aig,
          (go aig distance curr hcurr acc).stream.getRef idx hidx,
          assign
        ⟧
          =
        (BitVec.shiftLeftRec lhs rhs (n - 1)).getLsb idx := by
  intro idx hidx
  generalize hgo : go aig distance curr hcurr acc = res
  unfold go at hgo
  dsimp at hgo
  split at hgo
  . rw [← hgo]
    rw [go_eq_eval_getLsb]
    . intro idx hidx
      simp only [BitVec.shiftLeftRec_succ]
      rw [twoPowShift_eq (lhs := BitVec.shiftLeftRec lhs rhs curr)]
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

end blastShiftLeft

theorem blastShiftLeft_eq_eval_getLsb (aig : AIG α) (target : ArbitraryShiftTarget aig w0)
    (lhs : BitVec w0) (rhs : BitVec target.n) (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w0), ⟦aig, target.target.getRef idx hidx, assign⟧ = lhs.getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < target.n), ⟦aig, target.distance.getRef idx hidx, assign⟧ = rhs.getLsb idx)
    : ∀ (idx : Nat) (hidx : idx < w0),
        ⟦
          (blastShiftLeft aig target).aig,
          (blastShiftLeft aig target).stream.getRef idx hidx,
          assign
        ⟧
          =
        (lhs <<< rhs).getLsb idx := by
  intro idx hidx
  rw [BitVec.shiftLeft_eq_shiftLeftRec]
  generalize hg : blastShiftLeft aig target = res
  rcases target with ⟨n, target, distance⟩
  unfold blastShiftLeft at hg
  dsimp at hg
  split at hg
  . next hzero =>
    dsimp
    subst hzero
    rw [← hg]
    simp only [hleft, Nat.zero_sub, BitVec.shiftLeftRec_zero, BitVec.and_twoPow, Nat.le_refl,
      BitVec.getLsb_ge, Bool.false_eq_true, ↓reduceIte, BitVec.reduceHShiftLeft',
      BitVec.getLsb_shiftLeft, Nat.sub_zero, Bool.iff_and_self, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt, Nat.zero_le, and_true]
    apply BitVec.lt_of_getLsb
  . rw [← hg]
    rw [blastShiftLeft.go_eq_eval_getLsb]
    . intro idx hidx
      simp only [BitVec.shiftLeftRec_zero]
      rw [blastShiftLeft.twoPowShift_eq]
      . simp [hleft]
      . simp [hright]
    . intros
      rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := blastShiftLeft.twoPowShift)]
      . simp [hright]
      . simp [Ref.hgate]

end bitblast
end BVExpr
