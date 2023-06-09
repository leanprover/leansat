/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import Aesop
import LeanSAT.Sat.Basic
import LeanSAT.Util.PosFin

/-- The `Assignment` inductive datatype is used in the `assignments` field of default formulas (defined in
    Formula.Implementation.lean) to store and quickly access information about whether unit literals are
    contained in (or entailed by) a formula.

    The elements of `Assignment` can be viewed as a lattice where `both` is top, satisfying both `hasPosAssignment`
    and `hasNegAssignment`, `pos` satisfies only the former, `neg` satisfies only the latter, and `unassigned` is
    bottom, satisfying neither. If one wanted to modify the default formula structure to use a BitArray rather than
    an `Assignment Array` for the `assignments` field, a reasonable 2-bit representation of the `Assignment` type
    would be:
    - both: 11
    - pos: 10
    - neg: 01
    - unassigned: 00

    Then `hasPosAssignment` could simply query the first bit and `hasNegAssignment` could simply query the second bit. -/
inductive Assignment
  | pos
  | neg
  | both
  | unassigned
deriving Inhabited, DecidableEq, BEq

namespace Assignment

instance : ToString Assignment where
  toString := fun a =>
    match a with
    | pos => "pos"
    | neg => "neg"
    | both => "both"
    | unassigned => "unassigned"

def hasPosAssignment (assignment : Assignment) : Bool :=
  match assignment with
  | pos => true
  | neg => false
  | both => true
  | unassigned => false

def hasNegAssignment (assignment : Assignment) : Bool :=
  match assignment with
  | pos => false
  | neg => true
  | both => true
  | unassigned => false

/-- Updates the old assignment of l to reflect the fact that (l, true) is now part of the formula -/
def addPosAssignment (oldAssignment : Assignment) : Assignment :=
  match oldAssignment with
  | pos => pos
  | neg => both
  | both => both
  | unassigned => pos

/-- Updates the old assignment of l to reflect the fact that (l, true) is no longer part of the formula -/
def removePosAssignment (oldAssignment : Assignment) : Assignment :=
  match oldAssignment with
  | pos => unassigned
  | neg => neg -- Note: This case should not occur
  | both => neg
  | unassigned => unassigned -- Note: this case should not occur

/-- Updates the old assignment of l to reflect the fact that (l, false) is now part of the formula -/
def addNegAssignment (oldAssignment : Assignment) : Assignment :=
  match oldAssignment with
  | pos => both
  | neg => neg
  | both => both
  | unassigned => neg

/-- Updates the old assignment of l to reflect the fact that (l, false) is no longer part of the formula -/
def removeNegAssignment (oldAssignment : Assignment) : Assignment :=
  match oldAssignment with
  | pos => pos -- Note: This case should not occur
  | neg => unassigned
  | both => pos
  | unassigned => unassigned -- Note: This case should not occur

def addAssignment (b : Bool) : Assignment → Assignment :=
  if b then addPosAssignment
  else addNegAssignment

def removeAssignment (b : Bool) : Assignment → Assignment :=
  if b then removePosAssignment
  else removeNegAssignment

def hasAssignment (b : Bool) : Assignment → Bool :=
  if b then hasPosAssignment
  else hasNegAssignment

theorem removePos_addPos_cancel {assignment : Assignment} (h : ¬(hasPosAssignment assignment)) :
  removePosAssignment (addPosAssignment assignment) = assignment := by
  rw [removePosAssignment, addPosAssignment]
  rw [hasPosAssignment] at h
  split
  . next h' =>
    split at h'
    . split at h
      . simp only at h
      . next h'' => simp only at h''
      . simp only at h
      . next h'' => rw [h'']
    . simp only at h'
    . simp only at h'
    . rfl
  . next h' =>
    split at h'
    . rw [h']
    . rfl
    . rw [h']
    . split at h
      . simp only at h
      . next h'' => rw [h'']
      . next h'' => simp only at h''
      . simp only at h'
  . next h' =>
    split at h'
    . simp only at h'
    . rfl
    . split at h
      . next h'' => simp only at h''
      . next h'' => rw [h'']
      . simp only at h
      . next h'' => simp only at h''
    . simp only at h'
  . next h' =>
    split at h'
    . rw [h']
    . simp only at h'
    . rw [h']
    . rfl

theorem removeNeg_addNeg_cancel {assignment : Assignment} (h : ¬(hasNegAssignment assignment)) :
  removeNegAssignment (addNegAssignment assignment) = assignment := by
  rw [removeNegAssignment, addNegAssignment]
  rw [hasNegAssignment] at h
  split
  . next h' =>
    split at h'
    . rfl
    . rw [h']
    . rw [h']
    . simp only at h'
  . next h' =>
    split at h'
    . simp only at h'
    . split at h
      . next h'' => simp only at h''
      . simp only at h
      . next h'' => simp only at h''
      . next h'' => rw [h'']
    . simp only at h'
    . rfl
  . next h' =>
    split at h'
    . rfl
    . simp only at h'
    . split at h
      . next h'' => rw [h'']
      . simp only at h
      . simp only at h
      . next h'' => simp only at h''
    . simp only at h'
  . next h' =>
    split at h'
    . simp only at h'
    . rw [h']
    . rw [h']
    . rfl

theorem remove_add_cancel {assignment : Assignment} {b : Bool} (h : ¬(hasAssignment b assignment)) :
  removeAssignment b (addAssignment b assignment) = assignment := by
  by_cases hb : b
  . simp only [removeAssignment, hb, addAssignment, ite_true]
    simp only [hasAssignment, hb, ite_true] at h
    exact removePos_addPos_cancel h
  . simp only [removeAssignment, hb, addAssignment, ite_true]
    simp only [hasAssignment, hb, ite_false] at h
    exact removeNeg_addNeg_cancel h

theorem add_of_both_eq_both (b : Bool) : addAssignment b both = both := by
  rw [addAssignment]
  split
  . simp only
  . simp only

theorem has_of_both (b : Bool) : hasAssignment b both = true := by
  rw [hasAssignment]
  split
  . simp only
  . simp only

theorem has_of_add (assignment : Assignment) (b : Bool) : hasAssignment b (addAssignment b assignment) := by
  rw [addAssignment, hasAssignment]
  split
  . rw [hasPosAssignment, addPosAssignment]
    split
    . rfl
    . next heq =>
      split at heq
      repeat { simp only at heq }
    . rfl
    . next heq =>
      split at heq
      repeat { simp only at heq }
  . rw [hasNegAssignment, addNegAssignment]
    split
    . next heq =>
      split at heq
      repeat { simp only at heq }
    . rfl
    . rfl
    . next heq =>
      split at heq
      repeat { simp only at heq }

theorem not_hasPos_of_removePos (assignment : Assignment) : ¬hasPosAssignment (removePosAssignment assignment) := by
  simp only [removePosAssignment._eq_1, hasPosAssignment._eq_1, Bool.not_eq_true]
  split
  . next h =>
    split at h
    . simp only at h
    . simp only at h
    . simp only at h
    . simp only at h
  . rfl
  . next h =>
    split at h
    . simp only at h
    . simp only at h
    . simp only at h
    . simp only at h
  . rfl

theorem not_hasNeg_of_removeNeg (assignment : Assignment) : ¬hasNegAssignment (removeNegAssignment assignment) := by
  simp only [removeNegAssignment._eq_1, hasNegAssignment._eq_1, Bool.not_eq_true]
  split
  . rfl
  . next h =>
    split at h
    . simp only at h
    . simp only at h
    . simp only at h
    . simp only at h
  . next h =>
    split at h
    . simp only at h
    . simp only at h
    . simp only at h
    . simp only at h
  . rfl

theorem not_has_of_remove (assignment : Assignment) (b : Bool) : ¬hasAssignment b (removeAssignment b assignment) := by
  by_cases hb : b
  . simp only [hb, removeAssignment, ite_true, hasAssignment._eq_1, Bool.not_eq_true]
    have h := not_hasPos_of_removePos assignment
    simp only [Bool.not_eq_true] at h
    exact h
  . simp only [hb, removeAssignment, ite_false, hasAssignment._eq_1, Bool.not_eq_true]
    have h := not_hasNeg_of_removeNeg assignment
    simp only [Bool.not_eq_true] at h
    exact h

theorem has_of_remove_irrelevant (assignment : Assignment) (b : Bool) :
  hasAssignment b (removeAssignment (!b) assignment) → hasAssignment b assignment := by
  by_cases hb : b
  . simp only [hb, removeAssignment, Bool.not_true, ite_false, hasAssignment._eq_1, ite_true]
    match heq : assignment with
    | unassigned => simp only
    | pos => simp only
    | neg => simp only
    | both => simp only
  . simp only [Bool.not_eq_true] at hb
    simp only [hb, removeAssignment, Bool.not_true, ite_false, hasAssignment._eq_1, ite_true]
    match heq : assignment with
    | unassigned => simp only
    | pos => simp only
    | neg => simp only
    | both => simp only

theorem unassigned_of_has_neither (assignment : Assignment) (lacks_pos : ¬(hasPosAssignment assignment))
  (lacks_neg : ¬(hasNegAssignment assignment)) : assignment = unassigned := by
  simp only [hasPosAssignment, Bool.not_eq_true] at lacks_pos
  split at lacks_pos
  . simp only at lacks_pos
  . simp only at lacks_neg
  . simp only at lacks_pos
  . rfl

theorem hasPos_of_addNeg (assignment : Assignment) : hasPosAssignment (addNegAssignment assignment) = hasPosAssignment assignment := by
  rw [hasPosAssignment, addNegAssignment]
  split
  . next heq =>
    split at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq
  . next heq =>
    split at heq
    . simp only at heq
    . simp only
    . simp only at heq
    . simp only
  . next heq =>
    split at heq
    . simp only
    . simp only at heq
    . simp only
    . simp only at heq
  . next heq =>
    split at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq

theorem hasNeg_of_addPos (assignment : Assignment) : hasNegAssignment (addPosAssignment assignment) = hasNegAssignment assignment := by
  rw [hasNegAssignment, addPosAssignment]
  split
  . next heq =>
    split at heq
    . simp only
    . simp only at heq
    . simp only at heq
    . simp only
  . next heq =>
    split at heq
    . simp only at heq
    . simp only
    . simp only at heq
    . simp only at heq
  . next heq =>
    split at heq
    . simp only at heq
    . simp only
    . simp only
    . simp only at heq
  . next heq =>
    split at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq

theorem has_iff_has_of_add_complement (assignment : Assignment) (b : Bool) :
  hasAssignment b assignment ↔ hasAssignment b (addAssignment (¬b) assignment) := by
  by_cases hb : b
  . simp only [hb, hasAssignment._eq_1, ite_true, not_true, decide_False, addAssignment._eq_1, ite_false, hasPos_of_addNeg]
  . simp only [Bool.not_eq_true] at hb
    simp only [hb, hasAssignment._eq_1, ite_true, not_true, decide_False, addAssignment._eq_1, ite_false, hasNeg_of_addPos]

theorem addPos_of_addNeg_eq_both (assignment : Assignment) : addPosAssignment (addNegAssignment assignment) = both := by
  rw [addPosAssignment, addNegAssignment]
  split
  . next heq =>
    split at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq
  . rfl
  . rfl
  . next heq =>
    split at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq

theorem addNeg_of_addPos_eq_both (assignment : Assignment) : addNegAssignment (addPosAssignment assignment) = both := by
  rw [addNegAssignment, addPosAssignment]
  split
  . rfl
  . next heq =>
    split at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq
  . rfl
  . next heq =>
    split at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq
    . simp only at heq

instance {n : Nat} : HSat (PosFin n) (Array Assignment) where
  eval := fun p arr => ∀ i : PosFin n, ¬(hasAssignment (¬p i) arr[i.1]!)

end Assignment
