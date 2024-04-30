/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import Test.PHPDemo.Nodup

open Dimacs LRAT DefaultClause DefaultFormula Result Lean Classical

inductive pigeon where
  | p1
  | p2
  | p3
  | p4

inductive hole where
  | h1
  | h2
  | h3

open pigeon hole

variable (f : pigeon → hole)

theorem c_in_php3_formula_options (c : DefaultClause 13) (c_in_php3_formula : c ∈ DefaultFormula.toList php3_formula) :
  c = c1 ∨ c = c2 ∨ c = c3 ∨ c = c4 ∨ c = c5 ∨ c = c6 ∨ c = c7 ∨ c = c8 ∨ c = c9 ∨ c = c10 ∨ c = c11 ∨ c = c12 ∨ c = c13 ∨
  c = c14 ∨ c = c15 ∨ c = c16 ∨ c = c17 ∨ c = c18 ∨ c = c19 ∨ c = c20 ∨ c = c21 ∨ c = c22 := by
  rw [DefaultFormula.toList, php3_formula, DefaultFormula.ofArray] at c_in_php3_formula
  simp only [List.map, List.append_nil] at c_in_php3_formula
  rw [List.mem_filterMap] at c_in_php3_formula
  rcases c_in_php3_formula with ⟨c', c_in_php3_formula, c'_def⟩
  simp only [id] at c'_def
  rw [Array.toList_eq, Array.toArray_data] at c_in_php3_formula
  simp only at c_in_php3_formula
  rw [List.mem_cons] at c_in_php3_formula
  rcases c_in_php3_formula with h | c_in_php3_formula; simp only [h, id] at c'_def
  rw [c'_def] at c_in_php3_formula
  simp at c_in_php3_formula
  exact c_in_php3_formula

theorem php3_of_php3_formula_unsat : unsatisfiable (PosFin 13) php3_formula → ∃ x1 : pigeon, ∃ x2 : pigeon, x1 ≠ x2 ∧ (f x1) = (f x2) := by
  by_contra h
  simp only [ne_eq, Misc.not_forall, not_exists, not_and, exists_prop] at h
  rcases h with ⟨php3_unsat, h⟩

  let p : PosFin 13 → Bool := fun
    | ⟨1, _⟩ => f p1 = h1
    | ⟨2, _⟩ => f p1 = h2
    | ⟨3, _⟩ => f p1 = h3
    | ⟨4, _⟩ => f p2 = h1
    | ⟨5, _⟩ => f p2 = h2
    | ⟨6, _⟩ => f p2 = h3
    | ⟨7, _⟩ => f p3 = h1
    | ⟨8, _⟩ => f p3 = h2
    | ⟨9, _⟩ => f p3 = h3
    | ⟨10, _⟩ => f p4 = h1
    | ⟨11, _⟩ => f p4 = h2
    | ⟨12, _⟩ => f p4 = h3

  specialize php3_unsat p
  simp only [HSat.eval, p] at php3_unsat
  rw [List.all_eq_not_any_not, Bool.not_eq_true, Bool.not_eq_false', List.any_eq_true] at php3_unsat
  rcases php3_unsat with ⟨c, c_in_php3_formula, php3_unsat⟩
  simp only [List.any_eq_true, Misc.Prod.exists, Misc.Bool.exists_bool, Misc.Bool.decide_coe, Bool.not_eq_true',
    decide_eq_false_iff_not, not_exists, not_or, not_and] at php3_unsat
  have c_in_php3_formula := c_in_php3_formula_options c c_in_php3_formula
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c1Nodup c (Eq.symm hc)
    simp only [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10 ,v11, v12, Array.toList_eq, Array.data_toArray, List.find?,
      List.mem_cons, Prod.mk.injEq, and_false, List.mem_singleton, or_self, Bool.not_eq_true, false_implies, and_true, true_and,
      forall_eq_or_imp, decide_eq_false_iff_not, forall_eq, List.mem_nil_iff] at php3_unsat
    cases hfp1 : f p1
    repeat {simp (config := { decide := true }) only [hfp1, not_true, not_false_eq_true, implies_true, and_self, and_true] at php3_unsat}
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c2Nodup c (Eq.symm hc)
    simp only [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10 ,v11, v12, Array.toList_eq, Array.data_toArray, List.find?,
      List.mem_cons, Prod.mk.injEq, and_false, List.mem_singleton, or_self, Bool.not_eq_true, false_implies, and_true, true_and,
      forall_eq_or_imp, decide_eq_false_iff_not, forall_eq, List.mem_nil_iff] at php3_unsat
    cases hfp2 : f p2
    repeat {simp (config := { decide := true }) only [hfp2, not_true, not_false_eq_true, implies_true, and_self, and_true] at php3_unsat}
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c3Nodup c (Eq.symm hc)
    simp only [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10 ,v11, v12, Array.toList_eq, Array.data_toArray, List.find?,
      List.mem_cons, Prod.mk.injEq, and_false, List.mem_singleton, or_self, Bool.not_eq_true, false_implies, and_true, true_and,
      forall_eq_or_imp, decide_eq_false_iff_not, forall_eq, List.mem_nil_iff] at php3_unsat
    cases hfp3 : f p3
    repeat {simp (config := { decide := true }) only [hfp3, not_true, not_false_eq_true, implies_true, and_self, and_true] at php3_unsat}
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c4Nodup c (Eq.symm hc)
    simp only [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10 ,v11, v12, Array.toList_eq, Array.data_toArray, List.find?,
      List.mem_cons, Prod.mk.injEq, and_false, List.mem_singleton, or_self, Bool.not_eq_true, false_implies, and_true, true_and,
      forall_eq_or_imp, decide_eq_false_iff_not, forall_eq, List.mem_nil_iff] at php3_unsat
    cases hfp4 : f p4
    repeat {simp (config := { decide := true }) only [hfp4, not_true, not_false_eq_true, implies_true, and_self, and_true] at php3_unsat}

  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c5Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p1 p2 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c6Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p1 p3 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c7Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p1 p4 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c8Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p2 p3 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c9Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p2 p4 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c10Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p3 p4 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl

  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c11Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p1 p2 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c12Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p1 p3 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c13Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p1 p4 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c14Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p2 p3 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c15Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p2 p4 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c16Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p3 p4 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl

  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c17Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p1 p2 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c18Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p1 p3 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c19Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p1 p4 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | c_in_php3_formula
  . have hc' := Clause.ofArray_eq _ c20Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p2 p3 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  rcases c_in_php3_formula with hc | hc
  . have hc' := Clause.ofArray_eq _ c21Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p2 p4 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl
  . have hc' := Clause.ofArray_eq _ c22Nodup c (Eq.symm hc)
    simp [hc', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, Array.toList_eq, Array.data_toArray, List.find?, List.mem_cons,
      Prod.mk.injEq, and_true, List.mem_singleton, Bool.not_eq_true, and_false, or_self, false_implies, forall_eq_or_imp,
      decide_eq_false_iff_not, decide_not, Bool.not_eq_false', decide_eq_true_eq, forall_eq, List.mem_nil_iff] at php3_unsat
    specialize h p3 p4 (by simp only [not_false_eq_true])
    rw [php3_unsat.1, php3_unsat.2] at h
    exact h rfl

def php3_lrat_proof := certified_php3_lrat_proof.map Subtype.val

theorem php3_lrat_proof_wellFormed : ∀ a : DefaultClauseAction 13, a ∈ php3_lrat_proof → wellFormedAction a := by
  intro a a_in_php3_lrat_proof
  simp [php3_lrat_proof] at a_in_php3_lrat_proof
  rcases a_in_php3_lrat_proof with ⟨x, _, hx⟩
  rw [← hx]
  exact x.2

theorem php3_formula_unsat : lratChecker php3_formula php3_lrat_proof = success → unsatisfiable (PosFin 13) php3_formula := by
  have php3_formula_readyForRupAdd : readyForRupAdd php3_formula := ofArray_readyForRupAdd _
  have php3_formula_readyForRatAdd : readyForRatAdd php3_formula := ofArray_readyForRatAdd _
  exact lratCheckerSound php3_formula php3_formula_readyForRupAdd php3_formula_readyForRatAdd php3_lrat_proof php3_lrat_proof_wellFormed

theorem php3 : lratChecker php3_formula php3_lrat_proof == success → ∃ x1 : pigeon, ∃ x2 : pigeon, x1 ≠ x2 ∧ (f x1) = (f x2) := by
  intro lratChecker_success
  apply php3_of_php3_formula_unsat
  apply php3_formula_unsat
  apply eq_of_beq
  exact lratChecker_success

theorem php3_ofReduceBool : ∃ x1 : pigeon, ∃ x2 : pigeon, x1 ≠ x2 ∧ (f x1) = (f x2) := by
  apply php3
  native_decide
