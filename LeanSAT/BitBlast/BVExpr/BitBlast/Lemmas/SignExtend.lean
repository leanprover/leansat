/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.ZeroExtend
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.SignExtend

open AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastSignExtend

theorem go_getRef_aux (aig : AIG α) (w : Nat) (hw : 0 < w) (input : RefStream aig w) (newWidth : Nat)
    (curr : Nat) (hcurr : curr ≤ newWidth) (s : RefStream aig curr)
    : ∀ (idx : Nat) (hidx1 : idx < curr),
        (go w hw input newWidth curr hcurr s).getRef idx (by omega)
          =
        s.getRef idx hidx1 := by
  intro idx hidx
  unfold go
  split
  . dsimp
    split
    all_goals
      rw [go_getRef_aux]
      rw [AIG.RefStream.getRef_push_ref_lt]
  . dsimp
    simp only [RefStream.getRef, Ref.mk.injEq]
    have : curr = newWidth := by omega
    subst this
    simp

theorem go_getRef (aig : AIG α) (w : Nat) (hw : 0 < w) (input : RefStream aig w) (newWidth : Nat)
    (curr : Nat) (hcurr : curr ≤ newWidth) (s : RefStream aig curr)
    : ∀ (idx : Nat) (hidx1 : idx < newWidth),
        curr ≤ idx
          →
        (go w hw input newWidth curr hcurr s).getRef idx hidx1
          =
        if hidx2:idx < w then
          input.getRef idx (by omega)
        else
          input.getRef (w - 1) (by omega)
    := by
  intro idx hidx1 hcurr
  unfold go
  have : curr < newWidth := by omega
  simp only [this, ↓reduceDIte]
  cases Nat.eq_or_lt_of_le hcurr with
  | inl heq =>
    simp only [heq]
    split
    all_goals
      rw [go_getRef_aux]
      rw [AIG.RefStream.getRef_push_ref_eq']
      rw [heq]
  | inr heq =>
    split
    all_goals
      rw [go_getRef]
      omega

end blastSignExtend

theorem blastSignExtend_empty_eq_zeroExtend (aig : AIG α) (target : ExtendTarget aig newWidth)
      (htarget : target.w = 0)
  : blastSignExtend aig target = blastZeroExtend aig target := by
  unfold blastSignExtend
  simp [htarget]

theorem blastSignExtend_eq_eval_getLsb (aig : AIG α) (target : ExtendTarget aig newWidth)
  (assign : α → Bool) (htarget : 0 < target.w)
  : ∀ (idx : Nat) (hidx : idx < newWidth),
      ⟦
        (blastSignExtend aig target).aig,
        (blastSignExtend aig target).stream.getRef idx hidx,
        assign
      ⟧
        =
      if hidx:idx < target.w then
         ⟦aig, target.stream.getRef idx hidx, assign⟧
      else
         ⟦aig, target.stream.getRef (target.w - 1) (by omega), assign⟧
    := by
  intro idx hidx
  generalize hg : blastSignExtend aig target = res
  unfold blastSignExtend at hg
  dsimp at hg
  have : ¬ (target.w = 0) := by omega
  simp only [this, ↓reduceDIte] at hg
  rw [← hg]
  dsimp
  rw [blastSignExtend.go_getRef]
  . split <;> simp only
  . omega

end bitblast
end BVExpr
