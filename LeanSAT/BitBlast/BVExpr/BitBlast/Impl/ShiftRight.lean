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
      let s := s.push (input.get (distance + curr) (by omega))
      go aig input distance (curr + 1) (by omega) s
    else
      let res := aig.mkConstCached false
      let aig := res.aig
      let zeroRef := res.ref
      have hfinal := by
        apply AIG.LawfulOperator.le_size (f := AIG.mkConstCached)
      let s := s.cast hfinal
      let input := input.cast hfinal
      let s := s.push zeroRef
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
      let s := s.push (input.get (distance + curr) (by omega))
      go input distance (curr + 1) (by omega) s
    else
      let s := s.push (input.get (w - 1) (by omega))
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

namespace blastShiftRight

structure TwoPowShiftTarget (aig : AIG α) (w : Nat) where
  n : Nat
  lhs : AIG.RefStream aig w
  rhs : AIG.RefStream aig n
  pow : Nat

def twoPowShift (aig : AIG α) (target : TwoPowShiftTarget aig w) : AIG.RefStreamEntry α w :=
  let ⟨n, lhs, rhs, pow⟩ := target
  if h:pow < n then
    let res := blastShiftRightConst aig ⟨lhs, (2 ^ pow) % 2^n⟩
    let aig := res.aig
    let shifted := res.stream

    have := by
      apply AIG.LawfulStreamOperator.le_size (f := blastShiftRightConst)
    let rhs := rhs.cast this
    let lhs := lhs.cast this
    AIG.RefStream.ite aig ⟨rhs.get pow h, shifted, lhs⟩
  else
    ⟨aig, lhs⟩

instance : AIG.LawfulStreamOperator α TwoPowShiftTarget twoPowShift where
  le_size := by
    intros
    unfold twoPowShift
    dsimp
    split
    . apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.ite)
      apply AIG.LawfulStreamOperator.le_size (f := blastShiftRightConst)
    . simp
  decl_eq := by
    intros
    unfold twoPowShift
    dsimp
    split
    . rw [AIG.LawfulStreamOperator.decl_eq (f := AIG.RefStream.ite)]
      rw [AIG.LawfulStreamOperator.decl_eq (f := blastShiftRightConst)]
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastShiftRightConst)
      assumption
    . simp

end blastShiftRight

def blastShiftRight (aig : AIG α) (target : AIG.ArbitraryShiftTarget aig w)
    : AIG.RefStreamEntry α w :=
  let ⟨n, input, distance⟩ := target
  if n = 0 then
    ⟨aig, input⟩
  else
    let res := blastShiftRight.twoPowShift aig ⟨_, input, distance, 0⟩
    let aig := res.aig
    let acc := res.stream

    have := by
      apply AIG.LawfulStreamOperator.le_size (f := blastShiftRight.twoPowShift)

    let distance := distance.cast this
    go aig distance 0 (by omega) acc
where
  go {n : Nat} (aig : AIG α) (distance : AIG.RefStream aig n) (curr : Nat) (hcurr : curr ≤ n - 1)
      (acc : AIG.RefStream aig w)
      : AIG.RefStreamEntry α w :=
    if h:curr < n - 1 then
      let res := blastShiftRight.twoPowShift aig ⟨_, acc, distance, curr + 1⟩
      let aig := res.aig
      let acc := res.stream
      have := by
        apply AIG.LawfulStreamOperator.le_size (f := blastShiftRight.twoPowShift)
      let distance := distance.cast this

      go aig distance (curr + 1) (by omega) acc
    else
      ⟨aig, acc⟩
  termination_by n - 1 - curr

theorem blastShiftRight.go_le_size (aig : AIG α) (distance : AIG.RefStream aig n) (curr : Nat)
    (hcurr : curr ≤ n - 1) (acc : AIG.RefStream aig w)
    : aig.decls.size ≤ (go aig distance curr hcurr acc).aig.decls.size := by
  unfold go
  dsimp
  split
  . refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulStreamOperator.le_size (f := blastShiftRight.twoPowShift)
  . simp
termination_by n - 1 - curr

theorem blastShiftRight.go_decl_eq (aig : AIG α) (distance : AIG.RefStream aig n) (curr : Nat)
    (hcurr : curr ≤ n - 1) (acc : AIG.RefStream aig w)
    : ∀ (idx : Nat) (h1) (h2),
        (go aig distance curr hcurr acc).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig distance curr hcurr acc = res
  unfold go at hgo
  dsimp at hgo
  split at hgo
  . rw [← hgo]
    intros
    rw [blastShiftRight.go_decl_eq]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastShiftRight.twoPowShift)]
    apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastShiftRight.twoPowShift)
    assumption
  . simp [← hgo]
termination_by n - 1 - curr


instance : AIG.LawfulStreamOperator α AIG.ArbitraryShiftTarget blastShiftRight where
  le_size := by
    intros
    unfold blastShiftRight
    dsimp
    split
    . simp
    . refine Nat.le_trans ?_ (by apply blastShiftRight.go_le_size)
      apply AIG.LawfulStreamOperator.le_size (f := blastShiftRight.twoPowShift)
  decl_eq := by
    intros
    unfold blastShiftRight
    dsimp
    split
    . simp
    . rw [blastShiftRight.go_decl_eq]
      rw [AIG.LawfulStreamOperator.decl_eq (f := blastShiftRight.twoPowShift)]
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastShiftRight.twoPowShift)
      assumption

end bitblast
end BVExpr
