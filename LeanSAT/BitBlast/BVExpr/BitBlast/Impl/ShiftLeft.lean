/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.Basic
import LeanSAT.AIG.CachedGatesLemmas
import LeanSAT.AIG.LawfulStreamOperator
import LeanSAT.AIG.If

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastShiftLeftConst (aig : AIG α) (target : AIG.ShiftTarget aig w)
    : AIG.RefStreamEntry α w :=
  let ⟨input, distance⟩ := target
  go aig input distance 0 (by omega) .empty
where
  go (aig : AIG α) (input : AIG.RefStream aig w) (distance : Nat) (curr : Nat) (hcurr : curr ≤ w)
      (s : AIG.RefStream aig curr)
    : AIG.RefStreamEntry α w :=
  if hidx:curr < w then
    if hdist:curr < distance then
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
      let s := s.pushRef (input.getRef (curr - distance) (by omega))
      go aig input distance (curr + 1) (by omega) s
  else
    have hcurr : curr = w := by omega
    ⟨aig, hcurr ▸ s⟩
  termination_by w - curr

theorem blastShiftLeftConst.go_le_size (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : aig.decls.size ≤ (go aig input distance curr hcurr s).aig.decls.size := by
  unfold go
  split
  . dsimp
    split
    . refine Nat.le_trans ?_ (by apply go_le_size)
      apply AIG.LawfulOperator.le_size
    . refine Nat.le_trans ?_ (by apply go_le_size)
      omega
  . simp
termination_by w - curr

theorem blastShiftLeftConst.go_decl_eq (aig : AIG α) (distance : Nat) (input : AIG.RefStream aig w)
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
      rw [blastShiftLeftConst.go_decl_eq]
      rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      assumption
    . rw [← hgo]
      intro idx h1 h2
      rw [blastShiftLeftConst.go_decl_eq]
  . simp [← hgo]
termination_by w - curr

instance : AIG.LawfulStreamOperator α AIG.ShiftTarget blastShiftLeftConst where
  le_size := by
    intros
    unfold blastShiftLeftConst
    apply blastShiftLeftConst.go_le_size
  decl_eq := by
    intros
    unfold blastShiftLeftConst
    apply blastShiftLeftConst.go_decl_eq

def blastShiftLeft (aig : AIG α) (target : AIG.ArbitraryShiftTarget aig w)
    : AIG.RefStreamEntry α w :=
  let ⟨n, input, distance⟩ := target
  if h : n = 0 then
    ⟨aig, input⟩
  else
    have : 0 < n := by omega
    let res := blastShiftLeftConst aig ⟨input, 1⟩
    let aig := res.aig
    let shifted := res.stream

    have := by
      apply AIG.LawfulStreamOperator.le_size (f := blastShiftLeftConst)
    let input := input.cast this
    let distance := distance.cast this
    let res := AIG.RefStream.ite aig ⟨distance.getRef 0 (by assumption), shifted, input⟩
    let aig := res.aig
    let acc := res.stream

    have := by
      apply AIG.LawfulStreamOperator.le_size (f := AIG.RefStream.ite)
    let distance := distance.cast this
    if h:1 ≤ n - 1 then
      go aig distance 1 h acc
    else
      ⟨aig, acc⟩
where
  go {n : Nat} (aig : AIG α) (distance : AIG.RefStream aig n) (curr : Nat) (hcurr : curr ≤ n - 1)
      (acc : AIG.RefStream aig w)
      : AIG.RefStreamEntry α w :=
    if h:curr < n - 1 then
      let res := blastShiftLeftConst aig ⟨acc, 1 <<< curr⟩
      let aig := res.aig
      let shifted := res.stream
      have := by
        apply AIG.LawfulStreamOperator.le_size (f := blastShiftLeftConst)
      let distance := distance.cast this
      let acc := acc.cast this

      let res := AIG.RefStream.ite aig ⟨distance.getRef curr (by omega), shifted, acc⟩
      let aig := res.aig
      let acc := res.stream
      have := by
        apply AIG.LawfulStreamOperator.le_size (f := AIG.RefStream.ite)
      let distance := distance.cast this

      go aig distance (curr + 1) (by omega) acc
    else
      ⟨aig, acc⟩
  termination_by n - 1 - curr


theorem blastShiftLeft.go_le_size (aig : AIG α) (distance : AIG.RefStream aig n) (curr : Nat)
    (hcurr : curr ≤ n - 1) (acc : AIG.RefStream aig w)
    : aig.decls.size ≤ (go aig distance curr hcurr acc).aig.decls.size := by
  unfold go
  dsimp
  split
  . refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.ite)
    apply AIG.LawfulStreamOperator.le_size (f := blastShiftLeftConst)
  . simp
termination_by n - 1 - curr

theorem blastShiftLeft.go_decl_eq (aig : AIG α) (distance : AIG.RefStream aig n) (curr : Nat)
    (hcurr : curr ≤ n - 1) (acc : AIG.RefStream aig w)
    : ∀ (idx : Nat) (h1) (h2),
        (go aig distance curr hcurr acc).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig distance curr hcurr acc = res
  unfold go at hgo
  dsimp at hgo
  split at hgo
  . rw [← hgo]
    intros
    rw [blastShiftLeft.go_decl_eq]
    rw [AIG.LawfulStreamOperator.decl_eq (f := AIG.RefStream.ite)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastShiftLeftConst)]
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastShiftLeftConst)
      assumption
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := AIG.RefStream.ite)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastShiftLeftConst)
      assumption
  . simp [← hgo]
termination_by n - 1 - curr


instance : AIG.LawfulStreamOperator α AIG.ArbitraryShiftTarget blastShiftLeft where
  le_size := by
    intros
    unfold blastShiftLeft
    dsimp
    split
    . simp
    . split
      . refine Nat.le_trans ?_ (by apply blastShiftLeft.go_le_size)
        apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.ite)
        apply AIG.LawfulStreamOperator.le_size (f := blastShiftLeftConst)
      . apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.ite)
        apply AIG.LawfulStreamOperator.le_size (f := blastShiftLeftConst)
  decl_eq := by
    intros
    unfold blastShiftLeft
    dsimp
    split
    . simp
    . split
      . rw [blastShiftLeft.go_decl_eq]
        rw [AIG.LawfulStreamOperator.decl_eq (f := AIG.RefStream.ite)]
        rw [AIG.LawfulStreamOperator.decl_eq (f := blastShiftLeftConst)]
        . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastShiftLeftConst)
          assumption
        . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := AIG.RefStream.ite)
          apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastShiftLeftConst)
          assumption
      . dsimp
        rw [AIG.LawfulStreamOperator.decl_eq (f := AIG.RefStream.ite)]
        rw [AIG.LawfulStreamOperator.decl_eq (f := blastShiftLeftConst)]
        . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastShiftLeftConst)
          assumption

end bitblast
end BVExpr
