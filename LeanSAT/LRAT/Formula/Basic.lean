/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.LRAT.Formula.Implementation
import LeanSAT.LRAT.CNF

open Literal

namespace LRAT
namespace DefaultFormula

open Sat DefaultClause DefaultFormula Assignment Misc

/-- This invariant states that if the `assignments` field of a default formula `f` indicates that `f`
    contains an assignment `b` at index `i`, then the unit literal `(i, b)` must be included in `f`.
    Default formulas are expected to satisfy this invariant at all times except during intermediate
    stages of unit propogation (during which, default formulas are only expected to satisfy the more
    lenient `assignments_invariant` defined below). -/
def strong_assignments_invariant {n : Nat} (f : DefaultFormula n) : Prop :=
  ∃ hsize : f.assignments.size = n, ∀ i : PosFin n, ∀ b : Bool,
    hasAssignment b (f.assignments[i.1]'(by rw [hsize]; exact i.2.2)) →
    (unit (i, b)) ∈ toList f

/-- This invariant states that if the `assignments` field of a default formula `f` indicates that `f`
    contains an assignment `b` at index `i`, then the unit literal `(i, b)` is entailed by `f`. This is
    distinct from the `strong_assignments_invariant` defined above in that the entailment described here
    does not require explicitly containing the literal `(i, b)`. For example, if `f` contains `(i, b) ∨ (j, b')`
    as well as `(i, b) ∨ (j, ¬b')`, then the `assignments_invariant` would permit the `assignments` field of `f`
    to contain assignment `b` at index `i`, but the `strong_assignments_invariant` would not.-/
def assignments_invariant {n : Nat} (f : DefaultFormula n) : Prop :=
  ∃ hsize : f.assignments.size = n, ∀ i : PosFin n, ∀ b : Bool,
    hasAssignment b (f.assignments[i.1]'(by rw [hsize]; exact i.2.2)) →
    limplies (PosFin n) f (i, b)

theorem assignments_invariant_of_strong_assignments_invariant {n : Nat} (f : DefaultFormula n) :
  strong_assignments_invariant f → assignments_invariant f := by
  intro ⟨hsize, h⟩
  apply Exists.intro hsize
  intro i b hb p pf
  specialize h i b hb
  simp only [(· ⊨ ·), List.any_eq_true, Prod.exists, Bool.exists_bool,
    Bool.decide_coe, List.all_eq_true] at pf
  specialize pf (unit (i, b)) h
  simp [Clause.instHSat, unit_eq, Clause.toList] at pf
  exact pf

theorem assignments_invariant_entails_limplies {n : Nat} (f : DefaultFormula n)
  (f_assignments_invariant : assignments_invariant f) : limplies (PosFin n) f f.assignments := by
  intro p pf
  rcases f_assignments_invariant with ⟨hsize, f_assignments_invariant⟩
  simp only [(· ⊨ ·), Bool.not_eq_true]
  intro i
  specialize f_assignments_invariant i (decide (p i = false))
  by_cases hasAssignment (decide (p i = false)) (f.assignments[i.1]'(by rw [hsize]; exact i.2.2))
  . next h =>
    specialize f_assignments_invariant h p pf
    by_cases hpi : p i <;> simp [hpi, HSat.eval] at f_assignments_invariant
  . next h => simp_all [getElem!, i.2.2]

/-- performRupAdd adds to f.rupUnits and then clears f.rupUnits. If f begins with some units in f.rupUnits,
    then performRupAdd will clear more than it intended to which will break the correctness of rupAdd_result -/
def readyForRupAdd {n : Nat} (f : DefaultFormula n) : Prop := f.rupUnits = #[] ∧ strong_assignments_invariant f

/-- performRatAdd adds to f.rupUnits and f.ratUnits and then clears both. If f begins with some units in either,
    then performRatAdd will clear more than it intended to which will break the correctness of ratAdd_result -/
def readyForRatAdd {n : Nat} (f : DefaultFormula n) : Prop := f.ratUnits = #[] ∧ readyForRupAdd f

theorem insert_preserves_rupUnits {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) :
  (insert f c).rupUnits = f.rupUnits := by
  simp only [insert]
  split <;> simp only

theorem insert_preserves_ratUnits {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) :
  (insert f c).ratUnits = f.ratUnits := by
  simp only [insert]
  split <;> simp only

theorem ofArray_fold_fn_preserves_assignments_size {n : Nat} (assignments : Array Assignment) (cOpt : Option (DefaultClause n)) :
  (ofArray_fold_fn assignments cOpt).size = assignments.size := by
  rw [ofArray_fold_fn]
  split
  . rfl
  . split <;> simp [Array.modify_preserves_size]

theorem ofArray_readyForRupAdd {n : Nat} (arr : Array (Option (DefaultClause n))) : readyForRupAdd (ofArray arr) := by
  constructor
  . simp only [ofArray]
  . have hsize : (ofArray arr).assignments.size = n := by
      simp only [ofArray, Array.foldl_eq_foldl_data]
      have hb : (mkArray n unassigned).size = n := by simp only [Array.size_mkArray]
      have hl (acc : Array Assignment) (ih : acc.size = n) (cOpt : Option (DefaultClause n)) (_cOpt_in_arr : cOpt ∈ arr.data) :
        (ofArray_fold_fn acc cOpt).size = n := by rw [ofArray_fold_fn_preserves_assignments_size acc cOpt, ih]
      exact List.foldlRecOn arr.data ofArray_fold_fn (mkArray n unassigned) hb hl
    apply Exists.intro hsize
    let modified_assignments_invariant (assignments : Array Assignment) : Prop :=
      ∃ hsize : assignments.size = n,
        ∀ i : PosFin n, ∀ b : Bool, hasAssignment b (assignments[i.1]'(by rw [hsize]; exact i.2.2)) →
        (unit (i, b)) ∈ toList (ofArray arr)
    have hb : modified_assignments_invariant (mkArray n unassigned) := by
      have hsize : (mkArray n unassigned).size = n := by simp only [Array.size_mkArray]
      apply Exists.intro hsize
      intro i b h
      by_cases hb : b <;> simp [hasAssignment, hb, hasPosAssignment, hasNegAssignment] at h
    have hl (acc : Array Assignment) (ih : modified_assignments_invariant acc) (cOpt : Option (DefaultClause n))
      (cOpt_in_arr : cOpt ∈ arr.data) : modified_assignments_invariant (ofArray_fold_fn acc cOpt) := by
      have hsize : (ofArray_fold_fn acc cOpt).size = n := by rw [ofArray_fold_fn_preserves_assignments_size, ih.1]
      apply Exists.intro hsize
      intro i b h
      simp only [ofArray_fold_fn] at h
      split at h
      . exact ih.2 i b h
      . next cOpt c =>
        match heq : isUnit c with
        | none =>
          simp only [heq] at h
          exact ih.2 i b h
        | some (l, true) =>
          simp only [heq] at h
          have i_in_bounds : i.1 < acc.size := by simp only [ih.1, i.2.2]
          have l_in_bounds : l.1 < acc.size := by simp only [ih.1, l.2.2]
          rcases ih with ⟨hsize, ih⟩
          by_cases i = l.1
          . next i_eq_l =>
            simp only [i_eq_l, Array.get_modify_at_idx l_in_bounds] at h
            by_cases b
            . next b_eq_true =>
              rw [isUnit_iff, DefaultClause.toList] at heq
              simp only [toList, ofArray, Array.toList_eq, List.map, List.append_nil, List.mem_filterMap, id_eq, exists_eq_right]
              have i_eq_l : i = l := Subtype.ext i_eq_l
              simp only [unit, b_eq_true, i_eq_l]
              have c_def : c = ⟨c.clause, c.nodupkey, c.nodup⟩ := rfl
              simp only [heq] at c_def
              rw [c_def] at cOpt_in_arr
              exact cOpt_in_arr
            . next b_eq_false =>
              simp only [Bool.not_eq_true] at b_eq_false
              simp only [hasAssignment, b_eq_false, ite_false, hasNeg_of_addPos] at h
              specialize ih l false
              simp only [hasAssignment, ite_false] at ih
              rw [b_eq_false, Subtype.ext i_eq_l]
              exact ih h
          . next i_ne_l =>
            simp only [Array.get_modify_unchanged l_in_bounds i_in_bounds _ (Ne.symm i_ne_l)] at h
            exact ih i b h
        | some (l, false) =>
          simp only [heq] at h
          have i_in_bounds : i.1 < acc.size := by simp only [ih.1, i.2.2]
          have l_in_bounds : l.1 < acc.size := by simp only [ih.1, l.2.2]
          rcases ih with ⟨hsize, ih⟩
          by_cases i = l.1
          . next i_eq_l =>
            simp only [i_eq_l, Array.get_modify_at_idx l_in_bounds] at h
            by_cases b
            . next b_eq_true =>
              simp only [hasAssignment, b_eq_true, ite_true, hasPos_of_addNeg] at h
              specialize ih l true
              simp only [hasAssignment, ite_false] at ih
              rw [b_eq_true, Subtype.ext i_eq_l]
              exact ih h
            . next b_eq_false =>
              rw [isUnit_iff, DefaultClause.toList] at heq
              simp only [toList, ofArray, Array.toList_eq, List.map, List.append_nil, List.mem_filterMap, id_eq, exists_eq_right]
              have i_eq_l : i = l := Subtype.ext i_eq_l
              simp only [unit, b_eq_false, i_eq_l]
              have c_def : c = ⟨c.clause, c.nodupkey, c.nodup⟩ := rfl
              simp only [heq] at c_def
              rw [c_def] at cOpt_in_arr
              exact cOpt_in_arr
          . next i_ne_l =>
            simp only [Array.get_modify_unchanged l_in_bounds i_in_bounds _ (Ne.symm i_ne_l)] at h
            exact ih i b h
    rcases List.foldlRecOn arr.data ofArray_fold_fn (mkArray n unassigned) hb hl with ⟨_h_size, h'⟩
    intro i b h
    simp only [ofArray, Array.foldl_eq_foldl_data] at h
    exact h' i b h

theorem ofArray_readyForRatAdd {n : Nat} (arr : Array (Option (DefaultClause n))) : readyForRatAdd (ofArray arr) := by
  constructor
  . simp only [ofArray]
  . exact ofArray_readyForRupAdd arr

theorem insert_iff {n : Nat} (f : DefaultFormula n) (c1 : DefaultClause n) (c2 : DefaultClause n) :
  c2 ∈ toList (insert f c1) ↔ c2 = c1 ∨ c2 ∈ toList f := by
  simp only [toList, Array.toList_eq, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq, exists_eq_right,
    List.mem_map, Misc.Prod.exists, Misc.Bool.exists_bool]
  by_cases c2 = c1
  . next c2_eq_c1 =>
    constructor
    . intro _
      exact Or.inl c2_eq_c1
    . intro _
      apply Or.inl
      simp only [c2_eq_c1, insert]
      split <;> simp
  . next c2_ne_c1 =>
    constructor
    . intro h
      apply Or.inr
      rcases h with h | h | h
      . apply Or.inl
        simp only [insert] at h
        split at h
        all_goals
          simp only [Array.push_data, List.mem_append, List.mem_singleton, Option.some.injEq] at h
          rcases h with h | h
          . exact h
          . exact False.elim $ c2_ne_c1 h
      . rw [insert_preserves_rupUnits] at h
        exact Or.inr $ Or.inl h
      . rw [insert_preserves_ratUnits] at h
        exact Or.inr $ Or.inr h
    . intro h
      rcases h with h | h | h | h
      . exact False.elim $ c2_ne_c1 h
      . apply Or.inl
        simp only [insert]
        split
        all_goals
          simp only [Array.push_data, List.mem_append, List.mem_singleton, Option.some.injEq]
          exact Or.inl h
      . rw [insert_preserves_rupUnits]
        exact Or.inr $ Or.inl h
      . rw [insert_preserves_ratUnits]
        exact Or.inr $ Or.inr h

theorem limplies_of_insert {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) : limplies (PosFin n) (insert f c) f := by
  intro p
  simp only [formulaHSat_def, List.all_eq_true, decide_eq_true_eq]
  intro h c' c'_in_f
  have c'_in_fc : c' ∈ toList (insert f c) := by
    simp only [insert_iff, Array.toList_eq, Array.data_toArray, List.mem_singleton]
    exact Or.inr c'_in_f
  exact h c' c'_in_fc

theorem insert_preserves_assignments_size {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) :
  (insert f c).assignments.size = f.assignments.size := by
  simp only [insert]
  split <;> simp only [Array.modify_preserves_size]

theorem insert_readyForRupAdd {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) :
  readyForRupAdd f → readyForRupAdd (insert f c) := by
  intro f_readyForRupAdd
  simp only [insert]
  split
  . refine ⟨f_readyForRupAdd.1, f_readyForRupAdd.2.1, ?_⟩
    intro i b hb
    have hf := f_readyForRupAdd.2.2 i b hb
    simp only [toList, Array.toList_eq, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq, exists_eq_right,
      List.mem_map, Prod.exists, Bool.exists_bool] at hf
    simp only [toList, Array.toList_eq, Array.push_data, List.append_assoc, List.mem_append, List.mem_filterMap,
      List.mem_singleton, id_eq, exists_eq_right, Option.some.injEq, List.mem_map, Prod.exists, Bool.exists_bool]
    rcases hf with hf | hf
    . exact (Or.inl ∘ Or.inl) hf
    . exact Or.inr hf
  . next l hc =>
    have hsize : (Array.modify f.assignments l.1 addPosAssignment).size = n := by
      rw [Array.modify_preserves_size, f_readyForRupAdd.2.1]
    refine ⟨f_readyForRupAdd.1, hsize, ?_⟩
    intro i b hb
    have hf := f_readyForRupAdd.2.2 i b
    have i_in_bounds : i.1 < f.assignments.size := by rw [f_readyForRupAdd.2.1]; exact i.2.2
    have l_in_bounds : l.1 < f.assignments.size := by rw [f_readyForRupAdd.2.1]; exact l.2.2
    simp only at hb
    by_cases (i, b) = (l, true)
    . next ib_eq_c =>
      simp only [toList, Array.toList_eq, Array.push_data, List.append_assoc, List.mem_append, List.mem_filterMap,
        List.mem_singleton, id_eq, exists_eq_right, Option.some.injEq, List.mem_map, Prod.exists, Bool.exists_bool]
      apply Or.inl ∘ Or.inr
      rw [isUnit_iff, DefaultClause.toList, ← ib_eq_c] at hc
      apply DefaultClause.ext
      simp only [unit, hc]
    . next ib_ne_c =>
      have hb' : hasAssignment b (f.assignments[i.1]'i_in_bounds) := by
        by_cases l.1 = i.1
        . next l_eq_i =>
          have b_eq_false : b = false := by
            by_cases b = true
            . next b_eq_true =>
              simp only [b_eq_true, Subtype.ext l_eq_i, not_true] at ib_ne_c
            . next b_eq_false =>
              simp only [Bool.not_eq_true] at b_eq_false
              exact b_eq_false
          simp only [hasAssignment, b_eq_false, l_eq_i, Array.get_modify_at_idx i_in_bounds, ite_false, hasNeg_of_addPos] at hb
          simp only [hasAssignment, b_eq_false, ite_false, hb]
        . next l_ne_i =>
          simp only [Array.get_modify_unchanged l_in_bounds i_in_bounds _ l_ne_i] at hb
          exact hb
      specialize hf hb'
      simp only [toList, Array.toList_eq, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
        exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool] at hf
      simp only [toList, Array.toList_eq, Array.push_data, List.append_assoc, List.mem_append, List.mem_filterMap,
        List.mem_singleton, id_eq, exists_eq_right, Option.some.injEq, List.mem_map, Prod.exists, Bool.exists_bool]
      rcases hf with hf | hf
      . exact Or.inl $ Or.inl hf
      . exact Or.inr hf
  . next l hc =>
    have hsize : (Array.modify f.assignments l.1 addNegAssignment).size = n := by
      rw [Array.modify_preserves_size, f_readyForRupAdd.2.1]
    refine ⟨f_readyForRupAdd.1, hsize, ?_⟩
    intro i b hb
    have hf := f_readyForRupAdd.2.2 i b
    have i_in_bounds : i.1 < f.assignments.size := by rw [f_readyForRupAdd.2.1]; exact i.2.2
    have l_in_bounds : l.1 < f.assignments.size := by rw [f_readyForRupAdd.2.1]; exact l.2.2
    simp only at hb
    by_cases (i, b) = (l, false)
    . next ib_eq_c =>
      simp only [toList, Array.toList_eq, Array.push_data, List.append_assoc, List.mem_append, List.mem_filterMap,
        List.mem_singleton, id_eq, exists_eq_right, Option.some.injEq, List.mem_map, Prod.exists, Bool.exists_bool]
      apply Or.inl ∘ Or.inr
      rw [isUnit_iff, DefaultClause.toList, ← ib_eq_c] at hc
      apply DefaultClause.ext
      simp only [unit, hc]
    . next ib_ne_c =>
      have hb' : hasAssignment b (f.assignments[i.1]'i_in_bounds) := by
        by_cases l.1 = i.1
        . next l_eq_i =>
          have b_eq_false : b = true := by
            by_cases b = true
            . assumption
            . next b_eq_false =>
              simp only [b_eq_false, Subtype.ext l_eq_i, not_true] at ib_ne_c
          simp only [hasAssignment, b_eq_false, l_eq_i, Array.get_modify_at_idx i_in_bounds, ite_true, hasPos_of_addNeg] at hb
          simp only [hasAssignment, b_eq_false, ite_true, hb]
        . next l_ne_i =>
          simp only [Array.get_modify_unchanged l_in_bounds i_in_bounds _ l_ne_i] at hb
          exact hb
      specialize hf hb'
      simp only [toList, Array.toList_eq, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
        exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool] at hf
      simp only [toList, Array.toList_eq, Array.push_data, List.append_assoc, List.mem_append, List.mem_filterMap,
        List.mem_singleton, id_eq, exists_eq_right, Option.some.injEq, List.mem_map, Prod.exists, Bool.exists_bool]
      rcases hf with hf | hf
      . exact Or.inl $ Or.inl hf
      . exact Or.inr hf

theorem insert_readyForRatAdd {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) :
  readyForRatAdd f → readyForRatAdd (insert f c) := by
  intro h
  constructor
  . simp only [insert, h.1] <;> split <;> rfl
  . exact insert_readyForRupAdd f c h.2

theorem mem_of_insertRupUnits {n : Nat} (f : DefaultFormula n) (units : List (Literal (PosFin n)))
  (c : DefaultClause n) : c ∈ toList (insertRupUnits f units).1 → c ∈ units.map Clause.unit ∨ c ∈ toList f := by
  simp only [toList, insertRupUnits, Prod.mk.eta, Array.toList_eq, List.append_assoc, List.mem_append,
    List.mem_filterMap, id_eq, exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool]
  intro h
  have hb : ∀ l : Literal (PosFin n), l ∈ (f.rupUnits, f.assignments, false).1.data → (l ∈ f.rupUnits.data ∨ l ∈ units) := by
    intro l hl
    exact Or.inl hl
  have hl (acc : Array (Literal (PosFin n)) × Array Assignment × Bool)
    (ih : ∀ l : Literal (PosFin n), l ∈ acc.1.data → l ∈ f.rupUnits.data ∨ l ∈ units)
    (unit : Literal (PosFin n)) (unit_in_units : unit ∈ units) :
    ∀ l : Literal (PosFin n), l ∈ (insertUnit acc unit).1.data → (l ∈ f.rupUnits.data ∨ l ∈ units) := by
    intro l hl
    rw [insertUnit] at hl
    simp only [Prod.mk.eta] at hl
    split at hl
    . exact ih l hl
    . simp only [Array.push_data, List.mem_append, List.mem_singleton] at hl
      rcases hl with l_in_acc | l_eq_unit
      . exact ih l l_in_acc
      . rw [l_eq_unit]
        exact Or.inr unit_in_units
  have h_insertUnit_fold := List.foldlRecOn units insertUnit (f.rupUnits, f.assignments, false) hb hl
  rcases h with h | ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | h
  . exact Or.inr $ Or.inl h
  . rcases h_insertUnit_fold (i, false) h1 with h_insertUnit_fold | h_insertUnit_fold
    . apply Or.inr ∘ Or.inr ∘ Or.inl ∘ Exists.intro i ∘ Or.inl
      exact ⟨h_insertUnit_fold, h2⟩
    . apply Or.inl ∘ Exists.intro i ∘ Or.inl
      exact ⟨h_insertUnit_fold, h2⟩
  . rcases h_insertUnit_fold (i, true) h1 with h_insertUnit_fold | h_insertUnit_fold
    . apply Or.inr ∘ Or.inr ∘ Or.inl ∘ Exists.intro i ∘ Or.inr
      exact ⟨h_insertUnit_fold, h2⟩
    . apply Or.inl ∘ Exists.intro i ∘ Or.inr
      exact ⟨h_insertUnit_fold, h2⟩
  . exact (Or.inr ∘ Or.inr ∘ Or.inr) h

theorem mem_of_insertRatUnits {n : Nat} (f : DefaultFormula n) (units : List (Literal (PosFin n)))
  (c : DefaultClause n) : c ∈ toList (insertRatUnits f units).1 → c ∈ units.map Clause.unit ∨ c ∈ toList f := by
  simp only [toList, insertRatUnits, Prod.mk.eta, Array.toList_eq, List.append_assoc, List.mem_append,
    List.mem_filterMap, id_eq, exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool]
  intro h
  have hb : ∀ l : Literal (PosFin n), l ∈ (f.ratUnits, f.assignments, false).1.data → (l ∈ f.ratUnits.data ∨ l ∈ units) :=
    fun _ => Or.inl
  have hl (acc : Array (Literal (PosFin n)) × Array Assignment × Bool)
    (ih : ∀ l : Literal (PosFin n), l ∈ acc.1.data → l ∈ f.ratUnits.data ∨ l ∈ units)
    (unit : Literal (PosFin n)) (unit_in_units : unit ∈ units) :
    ∀ l : Literal (PosFin n), l ∈ (insertUnit acc unit).1.data → (l ∈ f.ratUnits.data ∨ l ∈ units) := by
    intro l hl
    rw [insertUnit] at hl
    simp only [Prod.mk.eta] at hl
    split at hl
    . exact ih l hl
    . simp only [Array.push_data, List.mem_append, List.mem_singleton] at hl
      rcases hl with l_in_acc | l_eq_unit
      . exact ih l l_in_acc
      . rw [l_eq_unit]
        exact Or.inr unit_in_units
  have h_insertUnit_fold := List.foldlRecOn units insertUnit (f.ratUnits, f.assignments, false) hb hl
  rcases h with h | h | ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  . exact Or.inr $ Or.inl h
  . exact (Or.inr ∘ Or.inr ∘ Or.inl) h
  . rcases h_insertUnit_fold (i, false) h1 with h_insertUnit_fold | h_insertUnit_fold
    . apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Exists.intro i ∘ Or.inl
      exact ⟨h_insertUnit_fold, h2⟩
    . apply Or.inl ∘ Exists.intro i ∘ Or.inl
      exact ⟨h_insertUnit_fold, h2⟩
  . rcases h_insertUnit_fold (i, true) h1 with h_insertUnit_fold | h_insertUnit_fold
    . apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Exists.intro i ∘ Or.inr
      exact ⟨h_insertUnit_fold, h2⟩
    . apply Or.inl ∘ Exists.intro i ∘ Or.inr
      exact ⟨h_insertUnit_fold, h2⟩

theorem deleteOne_preserves_rupUnits {n : Nat} (f : DefaultFormula n) (id : Nat) : (deleteOne f id).rupUnits = f.rupUnits := by
  simp only [deleteOne]
  split <;> simp only

theorem deleteOne_preserves_assignments_size {n : Nat} (f : DefaultFormula n) (id : Nat) :
  (deleteOne f id).assignments.size = f.assignments.size := by
  simp only [deleteOne]
  split <;> simp only [Array.modify_preserves_size]

theorem deleteOne_preserves_strong_assignments_invariant {n : Nat} (f : DefaultFormula n) (id : Nat) :
  strong_assignments_invariant f → strong_assignments_invariant (deleteOne f id) := by
  intro hf
  rcases hf with ⟨hsize, hf⟩
  have hsize' : (deleteOne f id).assignments.size = n := by
    simp only [← hsize]
    exact deleteOne_preserves_assignments_size f id
  apply Exists.intro hsize'
  intro i b hb
  have i_in_bounds : i.1 < f.assignments.size := by rw [hsize]; exact i.2.2
  simp only [deleteOne]
  match heq : f.clauses[id]! with
  | none =>
    simp only
    simp only [deleteOne, heq] at hb
    exact hf i b hb
  | some c =>
    by_cases hl : ∃ l : Literal (PosFin n), c = unit l
    . rcases hl with ⟨l, hl⟩
      simp only [unit] at hl
      simp only [hl]
      simp only [deleteOne, heq, hl] at hb
      by_cases l.1.1 = i.1
      . next l_eq_i =>
        simp only [l_eq_i, Array.get_modify_at_idx i_in_bounds] at hb
        have l_ne_b : l.2 ≠ b := by
          intro l_eq_b
          rw [← l_eq_b] at hb
          have hb' := not_has_of_remove f.assignments[i.1] l.2
          simp [hb] at hb'
        rw [← Bool.eq_not_iff] at l_ne_b
        rw [l_ne_b] at hb
        have hb := has_of_remove_irrelevant f.assignments[i.1] b hb
        specialize hf i b hb
        simp only [toList, Array.toList_eq, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
          exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool] at hf
        simp only [toList, Array.toList_eq, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
          exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool]
        rcases hf with hf | hf
        . apply Or.inl
          simp only [Array.set!, Array.setD]
          split
          . rcases List.getElem_of_mem hf with ⟨idx, hbound, hidx⟩
            simp only [← hidx, Array.data_set]
            rw [List.mem_iff_get]
            have idx_in_bounds : idx < List.length (List.set f.clauses.data id none) := by
              simp only [List.length_set]
              exact hbound
            apply Exists.intro ⟨idx, idx_in_bounds⟩
            by_cases id = idx
            . next id_eq_idx =>
              exfalso
              have idx_in_bounds2 : idx < f.clauses.size := by
                have f_clauses_rw : f.clauses = { data := f.clauses.data } := rfl
                conv => rhs; rw [f_clauses_rw, Array.size_mk]
                exact hbound
              simp only [getElem!, id_eq_idx, Array.data_length, idx_in_bounds2, ↓reduceDIte,
                Fin.eta, Array.get_eq_getElem, Array.getElem_eq_data_getElem] at heq
              rw [hidx, hl] at heq
              simp only [unit, Option.some.injEq, DefaultClause.mk.injEq, List.cons.injEq, and_true] at heq
              simp only [← heq, not] at l_ne_b
              split at l_ne_b
              . simp only at l_ne_b
              . simp only at l_ne_b
            . next id_ne_idx => simp [id_ne_idx]
          . exact hf
        . exact Or.inr hf
      . next l_ne_i =>
        have l_in_bounds : l.1.1 < f.assignments.size := by rw [hsize]; exact l.1.2.2
        simp only [Array.get_modify_unchanged l_in_bounds i_in_bounds _ l_ne_i] at hb
        specialize hf i b hb
        simp only [toList, Array.toList_eq, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
          exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool] at hf
        simp only [toList, Array.toList_eq, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
          exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool]
        rcases hf with hf | hf
        . apply Or.inl
          simp only [Array.set!, Array.setD]
          split
          . rcases List.getElem_of_mem hf with ⟨idx, hbound, hidx⟩
            simp only [← hidx, Array.data_set]
            rw [List.mem_iff_get]
            have idx_in_bounds : idx < List.length (List.set f.clauses.data id none) := by
              simp only [List.length_set]
              exact hbound
            apply Exists.intro ⟨idx, idx_in_bounds⟩
            by_cases id = idx
            . next id_eq_idx =>
              exfalso
              have idx_in_bounds2 : idx < f.clauses.size := by
                have f_clauses_rw : f.clauses = { data := f.clauses.data } := rfl
                conv => rhs; rw [f_clauses_rw, Array.size_mk]
                exact hbound
              simp only [getElem!, id_eq_idx, Array.data_length, idx_in_bounds2, ↓reduceDIte,
                Fin.eta, Array.get_eq_getElem, Array.getElem_eq_data_getElem] at heq
              rw [hidx, hl] at heq
              simp only [unit, Option.some.injEq, DefaultClause.mk.injEq, List.cons.injEq, and_true] at heq
              have i_eq_l : i = l.1 := by rw [← heq]
              simp only [i_eq_l, not_true] at l_ne_i
            . next id_ne_idx => simp [id_ne_idx]
          . exact hf
        . exact Or.inr hf
    . simp only [Prod.exists, Bool.exists_bool, not_exists, not_or, unit] at hl
      split
      . next some_eq_none =>
        simp only at some_eq_none
      . next l _ _ heq =>
        simp only [Option.some.injEq] at heq
        rw [heq] at hl
        specialize hl l.1
        simp only [DefaultClause.mk.injEq, List.cons.injEq, and_true] at hl
        by_cases hl2 : l.2
        . simp only [← hl2, Prod.mk.eta, not_true, and_false] at hl
        . simp only [Bool.not_eq_true] at hl2
          simp only [← hl2, Prod.mk.eta, not_true, false_and] at hl
      . have deleteOne_f_rw : deleteOne f id = ⟨Array.set! f.clauses id none, f.rupUnits, f.ratUnits, f.assignments⟩ := by
          simp only [deleteOne]
          split
          . next heq2 =>
            simp only [heq] at heq2
          . next l _ _ heq2 =>
            simp only [heq, Option.some.injEq] at heq2
            rw [heq2] at hl
            specialize hl l.1
            simp only [DefaultClause.mk.injEq, List.cons.injEq, and_true] at hl
            by_cases hl2 : l.2
            . simp only [← hl2, Prod.mk.eta, not_true, and_false] at hl
            . simp only [Bool.not_eq_true] at hl2
              simp only [← hl2, Prod.mk.eta, not_true, false_and] at hl
          . rfl
        simp only [deleteOne_f_rw] at hb
        specialize hf i b hb
        simp only [toList, Array.toList_eq, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
          exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool] at hf
        simp only [toList, Array.toList_eq, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
          exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool]
        rcases hf with hf | hf
        . apply Or.inl
          simp only [Array.set!, Array.setD]
          split
          . rcases List.getElem_of_mem hf with ⟨idx, hbound, hidx⟩
            simp only [← hidx, Array.data_set]
            rw [List.mem_iff_get]
            have idx_in_bounds : idx < List.length (List.set f.clauses.data id none) := by
              simp only [List.length_set]
              exact hbound
            apply Exists.intro ⟨idx, idx_in_bounds⟩
            by_cases id = idx
            . next id_eq_idx =>
              exfalso
              have idx_in_bounds2 : idx < f.clauses.size := by
                have f_clauses_rw : f.clauses = { data := f.clauses.data } := rfl
                conv => rhs; rw [f_clauses_rw, Array.size_mk]
                exact hbound
              simp only [getElem!, id_eq_idx, Array.data_length, idx_in_bounds2, ↓reduceDIte,
                Fin.eta, Array.get_eq_getElem, Array.getElem_eq_data_getElem] at heq
              rw [hidx] at heq
              simp only [Option.some.injEq] at heq
              rw [← heq] at hl
              specialize hl i
              simp only [unit, DefaultClause.mk.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true,
                Bool.not_eq_false, Bool.not_eq_true] at hl
              by_cases b_val : b
              . simp only [b_val, and_false] at hl
              . simp only [b_val, false_and] at hl
            . next id_ne_idx => simp [id_ne_idx]
          . exact hf
        . exact Or.inr hf

theorem delete_readyForRupAdd {n : Nat} (f : DefaultFormula n) (arr : Array Nat) :
  readyForRupAdd f → readyForRupAdd (delete f arr) := by
  intro h
  rw [delete, Array.foldl_eq_foldl_data]
  constructor
  . have hb : f.rupUnits = #[] := h.1
    have hl (acc : DefaultFormula n) (ih : acc.rupUnits = #[]) (id : Nat) (_id_in_arr : id ∈ arr.data) :
      (deleteOne acc id).rupUnits = #[] := by rw [deleteOne_preserves_rupUnits, ih]
    exact List.foldlRecOn arr.data deleteOne f hb hl
  . have hb : strong_assignments_invariant f := h.2
    have hl (acc : DefaultFormula n) (ih : strong_assignments_invariant acc) (id : Nat) (_id_in_arr : id ∈ arr.data) :
      strong_assignments_invariant (deleteOne acc id) := deleteOne_preserves_strong_assignments_invariant acc id ih
    exact List.foldlRecOn arr.data deleteOne f hb hl

theorem deleteOne_preserves_ratUnits {n : Nat} (f : DefaultFormula n) (id : Nat) : (deleteOne f id).ratUnits = f.ratUnits := by
  simp only [deleteOne]
  split <;> simp only

theorem delete_readyForRatAdd {n : Nat} (f : DefaultFormula n) (arr : Array Nat) :
  readyForRatAdd f → readyForRatAdd (delete f arr) := by
  intro h
  constructor
  . rw [delete, Array.foldl_eq_foldl_data]
    have hb : f.ratUnits = #[] := h.1
    have hl (acc : DefaultFormula n) (ih : acc.ratUnits = #[]) (id : Nat) (_id_in_arr : id ∈ arr.data) :
      (deleteOne acc id).ratUnits = #[] := by rw [deleteOne_preserves_ratUnits, ih]
    exact List.foldlRecOn arr.data deleteOne f hb hl
  . exact delete_readyForRupAdd f arr h.2

theorem deleteOne_subset (f : DefaultFormula n) (id : Nat) (c : DefaultClause n) :
  c ∈ toList (deleteOne f id) → c ∈ toList f := by
  simp only [deleteOne]
  intro h1
  split at h1 <;> first
  | exact h1
  | rw [toList, List.mem_append, List.mem_append, or_assoc] at h1
    rw [toList, List.mem_append, List.mem_append, or_assoc]
    rcases h1 with h1 | h1 | h1
    . apply Or.inl
      simp only [Array.toList_eq, List.mem_filterMap, id_eq, exists_eq_right] at h1
      simp only [Array.toList_eq, List.mem_filterMap, id_eq, exists_eq_right]
      rw [Array.set!, Array.setD] at h1
      split at h1
      . simp only [Array.data_set] at h1
        rcases List.getElem_of_mem h1 with ⟨i, h, h4⟩
        rw [List.getElem_set] at h4
        split at h4
        . exact False.elim h4
        . rw [← h4]
          apply List.getElem_mem
      . exact h1
    . exact (Or.inr ∘ Or.inl) h1
    . exact (Or.inr ∘ Or.inr) h1

theorem delete_subset (f : DefaultFormula n) (arr : Array Nat) (c : DefaultClause n) :
  c ∈ toList (delete f arr) → c ∈ toList f := by
  simp only [delete, Array.foldl_eq_foldl_data]
  have hb : c ∈ toList f → c ∈ toList f := id
  have hl (f' : DefaultFormula n) (ih : c ∈ toList f' → c ∈ toList f) (id : Nat) (_ : id ∈ arr.data) :
    c ∈ toList (deleteOne f' id) → c ∈ toList f := by intro h; exact ih $ deleteOne_subset f' id c h
  exact List.foldlRecOn arr.data deleteOne f hb hl
