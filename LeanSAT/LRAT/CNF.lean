/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.LRAT.Formula.Class

namespace LRAT

open Literal Clause Formula Misc Sat

namespace Literal

theorem sat_iff (p : α → Bool) (a : α) (b : Bool) : p ⊨ (a, b) ↔ (p a) = b := by
  simp only [HSat.eval]

theorem sat_negate_iff_not_sat {p : α → Bool} {l : Literal α} : p ⊨ negateLiteral l ↔ p ⊭ l := by
  simp only [negateLiteral, sat_iff]
  constructor
  . intro h pl
    rw [sat_iff, h, not] at pl
    split at pl <;> simp_all
  . intro h
    rw [sat_iff] at h
    rw [not]
    split <;> simp_all

theorem unsat_of_limplies_complement [HSat α t] (x : t) (l : Literal α) :
    limplies α x l → limplies α x (negateLiteral l) → unsatisfiable α x := by
  intro h1 h2 p px
  specialize h1 p px
  specialize h2 p px
  rw [sat_negate_iff_not_sat] at h2
  exact h2 h1

end Literal

namespace Clause

theorem sat_iff_exists [Clause α β] (p : α → Bool) (c : β) : p ⊨ c ↔ ∃ l ∈ toList c, p ⊨ l := by
  simp only [(· ⊨ ·)]
  simp only [List.any_eq_true, decide_eq_true_eq, Prod.exists, Bool.exists_bool]

theorem limplies_iff_mem [DecidableEq α] [Clause α β] (l : Literal α) (c : β) : limplies α l c ↔ l ∈ toList c := by
  simp only [limplies, sat_iff_exists, Prod.exists, Bool.exists_bool]
  constructor
  . intro h
    -- Construct an assignment p such that p ⊨ l and p ⊭ c ∖ {l}
    let p := fun x : α => if x = l.1 then l.2 else (x, false) ∈ toList c
    have pl : p ⊨ l := by simp only [(· ⊨ ·), ite_true, p]
    specialize h p pl
    rcases h with ⟨v, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    . simp only [(· ⊨ ·), p] at h2
      split at h2
      . next v_eq_l =>
        rw [← @Prod.mk.eta α Bool l, ← v_eq_l, h2]
        exact h1
      . next v_ne_l =>
        simp only [decide_eq_false_iff_not] at h2
        exfalso
        exact h2 h1
    . simp only [(· ⊨ ·), p] at h2
      split at h2
      . next v_eq_l =>
        rw [← @Prod.mk.eta α Bool l, ← v_eq_l, h2]
        exact h1
      . next v_ne_l =>
        simp only [decide_eq_true_eq] at h2
        exfalso
        rcases not_tautology c (v, true) with v_not_in_c | negv_not_in_c
        . exact v_not_in_c h1
        . simp only [negateLiteral, Bool.not_true] at negv_not_in_c
          exact negv_not_in_c h2
  . intro h p pl
    apply Exists.intro l.1
    by_cases hl : l.2
    . apply Or.inr
      rw [← hl]
      exact ⟨h, pl⟩
    . apply Or.inl
      simp only [Bool.not_eq_true] at hl
      rw [← hl]
      exact ⟨h, pl⟩

theorem entails_of_entails_delete [DecidableEq α] [Clause α β] {p : α → Bool} {c : β} {l : Literal α} :
    p ⊨ delete c l → p ⊨ c := by
  intro h
  simp only [(· ⊨ ·), List.any_eq_true, decide_eq_true_eq, Prod.exists, Bool.exists_bool] at h
  simp only [(· ⊨ ·), List.any_eq_true, decide_eq_true_eq, Prod.exists, Bool.exists_bool]
  rcases h with ⟨v, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  . simp only [delete_iff, ne_eq] at h1
    exact Exists.intro v $ Or.inl ⟨h1.2, h2⟩
  . simp only [delete_iff, ne_eq] at h1
    exact Exists.intro v $ Or.inr ⟨h1.2, h2⟩

end Clause

namespace Formula

theorem sat_iff_forall [Clause α β] [Formula α β σ] (p : α → Bool) (f : σ) :
    p ⊨ f ↔ ∀ c : β, c ∈ toList f → p ⊨ c := by
  simp only [(· ⊨ ·), formulaHSat_def p f]
  simp only [List.all_eq_true, decide_eq_true_eq]

theorem limplies_of_insert [Clause α β] [Formula α β σ] {c : β} {f : σ} : limplies α (insert f c) f := by
  intro p
  simp only [formulaHSat_def, List.all_eq_true, decide_eq_true_eq]
  intro h c' c'_in_f
  have c'_in_fc : c' ∈ toList (insert f c) := by
    simp only [insert_iff, Array.toList_eq, Array.data_toArray, List.mem_singleton]
    exact Or.inr c'_in_f
  exact h c' c'_in_fc

theorem limplies_delete [Clause α β] [Formula α β σ] {f : σ} {arr : Array Nat} : limplies α f (delete f arr) := by
  intro p
  simp only [formulaHSat_def, List.all_eq_true, decide_eq_true_eq]
  intro h c c_in_f_del
  have del_f_subset := delete_subset f arr
  specialize del_f_subset c c_in_f_del
  exact h c del_f_subset

end Formula
