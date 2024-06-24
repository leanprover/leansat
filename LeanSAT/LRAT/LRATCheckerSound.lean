/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.LRAT.LRATChecker
import LeanSAT.LRAT.CNF

open LRAT Result Formula Clause Sat

theorem addEmptyCaseSound [DecidableEq α] [Clause α β] [HSat α σ] [Formula α β σ] (f : σ) (f_readyForRupAdd : readyForRupAdd f)
    (rupHints: Array Nat) (rupAddSuccess : (Formula.performRupAdd f Clause.empty rupHints).snd = true) : unsatisfiable α f := by
  let f' := (performRupAdd f empty rupHints).1
  have f'_def := rupAdd_result f empty rupHints f' f_readyForRupAdd
  rw [← rupAddSuccess] at f'_def
  specialize f'_def rfl
  have f_liff_f' := rupAdd_sound f empty rupHints f' f_readyForRupAdd
  rw [← rupAddSuccess] at f_liff_f'
  specialize f_liff_f' rfl
  rw [f'_def] at f_liff_f'
  intro p pf
  specialize f_liff_f' p
  rw [f_liff_f', sat_iff_forall] at pf
  have empty_in_f' : empty ∈ toList (Formula.insert f empty) := by
    rw [Formula.insert_iff]
    exact Or.inl rfl
  specialize pf empty empty_in_f'
  simp only [HSat.eval, Clause.instHSat, List.any_eq_true, decide_eq_true_eq, Misc.Prod.exists, Misc.Bool.exists_bool,
    empty_eq, List.any_nil] at pf

theorem addRupCaseSound [DecidableEq α] [Clause α β] [HSat α σ] [Formula α β σ] (f : σ) (f_readyForRupAdd : readyForRupAdd f)
    (f_readyForRatAdd : readyForRatAdd f) (c : β) (f' : σ) (rupHints : Array Nat) (heq : performRupAdd f c rupHints = (f', true))
    (restPrf : List (Action β α)) (restPrfWellFormed : ∀ (a : Action β α), a ∈ restPrf → wellFormedAction a)
    (ih : ∀ (f : σ),
      readyForRupAdd f → readyForRatAdd f → (∀ (a : Action β α), a ∈ restPrf → wellFormedAction a) →
      lratChecker f restPrf = success → unsatisfiable α f)
    (f'_success : lratChecker f' restPrf = success) : unsatisfiable α f := by
  have f'_def := rupAdd_result f c rupHints f' f_readyForRupAdd heq
  have f'_readyForRupAdd : readyForRupAdd f' := by
    rw [f'_def]
    exact insert_readyForRupAdd f c f_readyForRupAdd
  have f'_readyForRatAdd : readyForRatAdd f' := by
    rw [f'_def]
    exact insert_readyForRatAdd f c f_readyForRatAdd
  specialize ih f' f'_readyForRupAdd f'_readyForRatAdd restPrfWellFormed f'_success
  have f_liff_f' : liff α f f' := rupAdd_sound f c rupHints f' f_readyForRupAdd heq
  intro p pf
  rw [f_liff_f' p] at pf
  exact ih p pf

theorem addRatCaseSound [DecidableEq α] [Clause α β] [HSat α σ] [Formula α β σ] (f : σ) (f_readyForRupAdd : readyForRupAdd f)
    (f_readyForRatAdd : readyForRatAdd f) (c : β) (pivot : Literal α) (f' : σ) (rupHints : Array Nat)
    (ratHints : Array (Nat × Array Nat)) (pivot_limplies_c : limplies α pivot c)
    (heq : performRatAdd f c pivot rupHints ratHints = (f', true))
    (restPrf : List (Action β α)) (restPrfWellFormed : ∀ (a : Action β α), a ∈ restPrf → wellFormedAction a)
    (ih : ∀ (f : σ),
      readyForRupAdd f → readyForRatAdd f → (∀ (a : Action β α), a ∈ restPrf → wellFormedAction a) →
      lratChecker f restPrf = success → unsatisfiable α f)
    (f'_success : lratChecker f' restPrf = success) : unsatisfiable α f := by
  rw [limplies_iff_mem] at pivot_limplies_c
  have f'_def := ratAdd_result f c pivot rupHints ratHints f' f_readyForRatAdd pivot_limplies_c heq
  have f'_readyForRupAdd : readyForRupAdd f' := by
    rw [f'_def]
    exact insert_readyForRupAdd f c f_readyForRupAdd
  have f'_readyForRatAdd : readyForRatAdd f' := by
    rw [f'_def]
    exact insert_readyForRatAdd f c f_readyForRatAdd
  specialize ih f' f'_readyForRupAdd f'_readyForRatAdd restPrfWellFormed f'_success
  have f_equisat_f' : equisat α f f' := ratAdd_sound f c pivot rupHints ratHints f' f_readyForRatAdd pivot_limplies_c heq
  intro p pf
  rw [equisat] at f_equisat_f'
  rw [← f_equisat_f'] at ih
  exact ih p pf

theorem delCaseSound [DecidableEq α] [Clause α β] [HSat α σ] [Formula α β σ] (f : σ) (f_readyForRupAdd : readyForRupAdd f)
    (f_readyForRatAdd : readyForRatAdd f) (ids : Array Nat) (restPrf : List (Action β α))
    (restPrfWellFormed : ∀ (a : Action β α), a ∈ restPrf → wellFormedAction a)
    (ih : ∀ (f : σ),
      readyForRupAdd f → readyForRatAdd f → (∀ (a : Action β α), a ∈ restPrf → wellFormedAction a) →
      lratChecker f restPrf = success → unsatisfiable α f)
    (h : lratChecker (Formula.delete f ids) restPrf = success) : unsatisfiable α f := by
  intro p pf
  have f_del_readyForRupAdd : readyForRupAdd (Formula.delete f ids) := delete_readyForRupAdd f ids f_readyForRupAdd
  have f_del_readyForRatAdd : readyForRatAdd (Formula.delete f ids) := delete_readyForRatAdd f ids f_readyForRatAdd
  exact ih (delete f ids) f_del_readyForRupAdd f_del_readyForRatAdd restPrfWellFormed h p (limplies_delete p pf)

theorem lratCheckerSound [DecidableEq α] [Clause α β] [HSat α σ] [Formula α β σ] (f : σ) (f_readyForRupAdd : readyForRupAdd f)
    (f_readyForRatAdd : readyForRatAdd f) (prf : List (Action β α)) (prfWellFormed : ∀ a : Action β α, a ∈ prf → wellFormedAction a) :
      lratChecker f prf = success → unsatisfiable α f := by
  induction prf generalizing f
  . unfold lratChecker
    simp only [false_implies]
  . next action restPrf ih =>
    simp only [List.find?, List.mem_cons, forall_eq_or_imp] at prfWellFormed
    rcases prfWellFormed with ⟨actionWellFormed, restPrfWellFormed⟩
    unfold lratChecker
    split
    . intro h
      exfalso
      simp only at h
    . next id rupHints restPrf' _ =>
      simp only [ite_eq_left_iff, Bool.not_eq_true]
      intro rupAddSuccess
      rw [← Bool.not_eq_true, imp_false, Classical.not_not] at rupAddSuccess
      exact addEmptyCaseSound f f_readyForRupAdd rupHints rupAddSuccess
    . next id c rupHints restPrf' hprf =>
      split
      next f' checkSuccess heq =>
      split
      . next hCheckSuccess =>
        intro f'_success
        simp only [List.cons.injEq] at hprf
        rw [← hprf.2] at f'_success
        rw [hCheckSuccess] at heq
        exact addRupCaseSound f f_readyForRupAdd f_readyForRatAdd c f' rupHints heq restPrf restPrfWellFormed ih f'_success
      . simp only [false_implies]
    . next id c pivot rupHints ratHints restPrf' hprf =>
      split
      next f' checkSuccess heq =>
      split
      . next hCheckSuccess =>
        intro f'_success
        simp only [List.cons.injEq] at hprf
        rw [← hprf.2] at f'_success
        rw [hCheckSuccess] at heq
        simp only [wellFormedAction, hprf.1] at actionWellFormed
        exact addRatCaseSound f f_readyForRupAdd f_readyForRatAdd c pivot f' rupHints ratHints actionWellFormed heq restPrf
          restPrfWellFormed ih f'_success
      . simp only [false_implies]
    . next ids restPrf' hprf =>
      intro h
      simp only [List.cons.injEq] at hprf
      rw [← hprf.2] at h
      exact delCaseSound f f_readyForRupAdd f_readyForRatAdd ids restPrf restPrfWellFormed ih h

theorem incrementalLRATCheckerSound [DecidableEq α] [Clause α β] [HSat α σ] [Formula α β σ] (f : σ) (f_readyForRupAdd : readyForRupAdd f)
    (f_readyForRatAdd : readyForRatAdd f) (a : Action β α) (aWellFormed : wellFormedAction a) :
      ((incrementalLRATChecker f a).2 = success → unsatisfiable α f) ∧
      ((incrementalLRATChecker f a).2 = out_of_proof → unsatisfiable α (incrementalLRATChecker f a).1 → unsatisfiable α f) := by
  constructor
  . intro incrementalChecker_success p pf
    unfold incrementalLRATChecker at incrementalChecker_success
    simp only at incrementalChecker_success
    split at incrementalChecker_success
    . next rupHints =>
      by_cases performRupAdd_success : (performRupAdd f empty rupHints).2
      . exact addEmptyCaseSound f f_readyForRupAdd rupHints performRupAdd_success p pf
      . simp only [performRupAdd_success, ite_false] at incrementalChecker_success
    . next c rupHints =>
      by_cases performRupAdd_success : (performRupAdd f c rupHints).2
      . simp only [performRupAdd_success, ite_true] at incrementalChecker_success
      . simp only [performRupAdd_success, ite_false] at incrementalChecker_success
    . next c pivot rupHints ratHints =>
      by_cases performRatAdd_success : (performRatAdd f c pivot rupHints ratHints).2
      . simp only [performRatAdd_success, ite_true] at incrementalChecker_success
      . simp only [performRatAdd_success, ite_false] at incrementalChecker_success
    . simp only at incrementalChecker_success
  . intro incrementalChecker_res incrementalChecker_res_unsat
    unfold incrementalLRATChecker at incrementalChecker_res
    simp only at incrementalChecker_res
    split at incrementalChecker_res
    . next rupHints =>
      by_cases h : (performRupAdd f empty rupHints).2
      . simp only [h, ite_true] at incrementalChecker_res
      . simp only [Bool.not_eq_true] at h
        simp only [h, ite_false] at incrementalChecker_res
    . next c rupHints =>
      by_cases performRupAdd_success : (performRupAdd f c rupHints).2
      . let f' := (performRupAdd f c rupHints).1
        have heq : performRupAdd f c rupHints = (f', true) := by rw [← performRupAdd_success]
        have f_liff_f' := rupAdd_sound f c rupHints f' f_readyForRupAdd heq
        unfold incrementalLRATChecker at incrementalChecker_res_unsat
        simp only [performRupAdd_success, ite_true] at incrementalChecker_res_unsat
        rw [liff_unsat f f' f_liff_f']
        exact incrementalChecker_res_unsat
      . simp only [Bool.not_eq_true] at performRupAdd_success
        simp only [performRupAdd_success, ite_false] at incrementalChecker_res
    . next c pivot rupHints ratHints =>
      by_cases performRatAdd_success : (performRatAdd f c pivot rupHints ratHints).2
      . let f' := (performRatAdd f c pivot rupHints ratHints).1
        have heq : performRatAdd f c pivot rupHints ratHints = (f', true) := by rw [← performRatAdd_success]
        simp only [wellFormedAction, limplies_iff_mem] at aWellFormed
        unfold incrementalLRATChecker at incrementalChecker_res_unsat
        simp only [performRatAdd_success, ite_true] at incrementalChecker_res_unsat
        have h := ratAdd_sound f c pivot rupHints ratHints f' f_readyForRatAdd aWellFormed heq
        rw [equisat] at h
        rw [h]
        exact incrementalChecker_res_unsat
      . simp only [Bool.not_eq_true] at performRatAdd_success
        simp only [performRatAdd_success, ite_false] at incrementalChecker_res
    . next ids =>
      unfold incrementalLRATChecker at incrementalChecker_res_unsat
      simp only at incrementalChecker_res_unsat
      intro p pf
      exact incrementalChecker_res_unsat p (limplies_delete p pf)
