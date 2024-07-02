/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.AIG.CachedGatesLemmas
import LeanSAT.AIG.LawfulStreamOperator

namespace BVExpr
namespace bitblast

variable [BEq α] [Hashable α] [DecidableEq α]

def blastShiftRightConst (aig : AIG α) (target : AIG.ShiftTarget aig w)
    : AIG.RefStreamEntry α w :=
  let ⟨input, distance⟩ := target
  go aig input distance 0 (by omega) .empty
where
  go (aig : AIG α) (input : AIG.RefStream aig w) (distance : Nat) (curr : Nat) (hcurr : curr ≤ w)
      (s : AIG.RefStream aig curr)
    : AIG.RefStreamEntry α w :=
  if hidx:curr < w then
    if hdist:(distance + curr) < w then
      let s := s.pushRef (input.getRef (distance + curr) (by omega))
      go aig input distance (curr + 1) (by omega) s
    else
      let res := aig.mkConstCached false
      let aig := res.aig
      let zeroRef := res.ref
      have hfinal := by
        apply AIG.LawfulOperator.le_size (f := AIG.mkConstCached)
      let s := s.cast hfinal
      let input := input.cast hfinal
      let s := s.pushRef zeroRef
      go aig input distance (curr + 1) (by omega) s
  else
    have hcurr : curr = w := by omega
    ⟨aig, hcurr ▸ s⟩
termination_by w - curr

theorem blastShiftRightConst.go_le_size (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : aig.decls.size ≤ (go aig input distance curr hcurr s).aig.decls.size := by
  unfold go
  split
  . dsimp
    split
    . refine Nat.le_trans ?_ (by apply go_le_size)
      omega
    . refine Nat.le_trans ?_ (by apply go_le_size)
      apply AIG.LawfulOperator.le_size
  . simp
termination_by w - curr

theorem blastShiftRightConst.go_decl_eq (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (h1) (h2),
        (go aig input distance curr hcurr s).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig input distance curr hcurr s = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    split at hgo
    . rw [← hgo]
      intro idx h1 h2
      rw [blastShiftRightConst.go_decl_eq]
    . rw [← hgo]
      intro idx h1 h2
      rw [blastShiftRightConst.go_decl_eq]
      rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      assumption
  . simp [← hgo]
termination_by w - curr

instance : AIG.LawfulStreamOperator α AIG.ShiftTarget blastShiftRightConst where
  le_size := by
    intros
    unfold blastShiftRightConst
    apply blastShiftRightConst.go_le_size
  decl_eq := by
    intros
    unfold blastShiftRightConst
    apply blastShiftRightConst.go_decl_eq

def blastArithShiftRightConst (aig : AIG α) (target : AIG.ShiftTarget aig w)
    : AIG.RefStreamEntry α w :=
  let ⟨input, distance⟩ := target
  ⟨aig, go input distance 0 (by omega) .empty⟩
where
  go {aig : AIG α} (input : AIG.RefStream aig w) (distance : Nat) (curr : Nat) (hcurr : curr ≤ w)
      (s : AIG.RefStream aig curr)
      : AIG.RefStream aig w :=
  if hidx:curr < w then
    if hdist:(distance + curr) < w then
      let s := s.pushRef (input.getRef (distance + curr) (by omega))
      go input distance (curr + 1) (by omega) s
    else
      let s := s.pushRef (input.getRef (w - 1) (by omega))
      go input distance (curr + 1) (by omega) s
  else
    have hcurr : curr = w := by omega
    hcurr ▸ s
termination_by w - curr

instance : AIG.LawfulStreamOperator α AIG.ShiftTarget blastArithShiftRightConst where
  le_size := by
    intros
    unfold blastArithShiftRightConst
    simp
  decl_eq := by
    intros
    unfold blastArithShiftRightConst
    simp

end bitblast
end BVExpr
