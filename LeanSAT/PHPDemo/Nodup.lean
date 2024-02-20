/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.PHPDemo.Formula

open Dimacs LRAT DefaultClause DefaultFormula Result Lean Classical

theorem eq_zero_or_one_of_lt_two {n : Nat} (h : n < 2) : n = 0 ∨ n = 1 := by
  rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ h with h | h
  . have h := Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ h
    rcases h with h | h
    . exfalso
      exact Nat.not_lt_zero n h
    . exact Or.inl h
  . exact Or.inr h

theorem eq_zero_or_one_or_two_of_lt_three {n : Nat} (h : n < 3) : n = 0 ∨ n = 1 ∨ n = 2 := by
  rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ h with h | h
  . rcases eq_zero_or_one_of_lt_two h with h' | h'
    . exact Or.inl h'
    . exact Or.inr $ Or.inl h'
  . exact Or.inr $ Or.inr h

theorem c1Nodup :
    ∀ i : Fin #[(v1, true), (v2, true), (v3, true)].size, ∀ j : Fin #[(v1, true), (v2, true), (v3, true)].size,
    i.1 ≠ j.1 → #[(v1, true), (v2, true), (v3, true)][i] ≠ #[(v1, true), (v2, true), (v3, true)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v1, true), (v2, true), (v3, true)].size = 3 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_or_two_of_lt_three i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_or_two_of_lt_three j_property
  rcases i_vals with hi | hi | hi
  all_goals
    rcases j_vals with hj | hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c2Nodup :
    ∀ i : Fin #[(v4, true), (v5, true), (v6, true)].size, ∀ j : Fin #[(v4, true), (v5, true), (v6, true)].size,
    i.1 ≠ j.1 → #[(v4, true), (v5, true), (v6, true)][i] ≠ #[(v4, true), (v5, true), (v6, true)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v4, true), (v5, true), (v6, true)].size = 3 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_or_two_of_lt_three i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_or_two_of_lt_three j_property
  rcases i_vals with hi | hi | hi
  all_goals
    rcases j_vals with hj | hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c3Nodup :
    ∀ i : Fin #[(v7, true), (v8, true), (v9, true)].size, ∀ j : Fin #[(v7, true), (v8, true), (v9, true)].size,
    i.1 ≠ j.1 → #[(v7, true), (v8, true), (v9, true)][i] ≠ #[(v7, true), (v8, true), (v9, true)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v7, true), (v8, true), (v9, true)].size = 3 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_or_two_of_lt_three i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_or_two_of_lt_three j_property
  rcases i_vals with hi | hi | hi
  all_goals
    rcases j_vals with hj | hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c4Nodup :
    ∀ i : Fin #[(v10, true), (v11, true), (v12, true)].size, ∀ j : Fin #[(v10, true), (v11, true), (v12, true)].size,
    i.1 ≠ j.1 → #[(v10, true), (v11, true), (v12, true)][i] ≠ #[(v10, true), (v11, true), (v12, true)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v10, true), (v11, true), (v12, true)].size = 3 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_or_two_of_lt_three i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_or_two_of_lt_three j_property
  rcases i_vals with hi | hi | hi
  all_goals
    rcases j_vals with hj | hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c5Nodup :
    ∀ i : Fin #[(v1, false), (v4, false)].size, ∀ j : Fin #[(v1, false), (v4, false)].size,
    i.1 ≠ j.1 → #[(v1, false), (v4, false)][i] ≠ #[(v1, false), (v4, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v1, false), (v4, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c6Nodup :
    ∀ i : Fin #[(v1, false), (v7, false)].size, ∀ j : Fin #[(v1, false), (v7, false)].size,
    i.1 ≠ j.1 → #[(v1, false), (v7, false)][i] ≠ #[(v1, false), (v7, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v1, false), (v7, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c7Nodup :
    ∀ i : Fin #[(v1, false), (v10, false)].size, ∀ j : Fin #[(v1, false), (v10, false)].size,
    i.1 ≠ j.1 → #[(v1, false), (v10, false)][i] ≠ #[(v1, false), (v10, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v1, false), (v10, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c8Nodup :
    ∀ i : Fin #[(v4, false), (v7, false)].size, ∀ j : Fin #[(v4, false), (v7, false)].size,
    i.1 ≠ j.1 → #[(v4, false), (v7, false)][i] ≠ #[(v4, false), (v7, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v4, false), (v7, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c9Nodup :
    ∀ i : Fin #[(v4, false), (v10, false)].size, ∀ j : Fin #[(v4, false), (v10, false)].size,
    i.1 ≠ j.1 → #[(v4, false), (v10, false)][i] ≠ #[(v4, false), (v10, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v4, false), (v10, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c10Nodup :
    ∀ i : Fin #[(v7, false), (v10, false)].size, ∀ j : Fin #[(v7, false), (v10, false)].size,
    i.1 ≠ j.1 → #[(v7, false), (v10, false)][i] ≠ #[(v7, false), (v10, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v7, false), (v10, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c11Nodup :
    ∀ i : Fin #[(v2, false), (v5, false)].size, ∀ j : Fin #[(v2, false), (v5, false)].size,
    i.1 ≠ j.1 → #[(v2, false), (v5, false)][i] ≠ #[(v2, false), (v5, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v2, false), (v5, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c12Nodup :
    ∀ i : Fin #[(v2, false), (v8, false)].size, ∀ j : Fin #[(v2, false), (v8, false)].size,
    i.1 ≠ j.1 → #[(v2, false), (v8, false)][i] ≠ #[(v2, false), (v8, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v2, false), (v8, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c13Nodup :
    ∀ i : Fin #[(v2, false), (v11, false)].size, ∀ j : Fin #[(v2, false), (v11, false)].size,
    i.1 ≠ j.1 → #[(v2, false), (v11, false)][i] ≠ #[(v2, false), (v11, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v2, false), (v11, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c14Nodup :
    ∀ i : Fin #[(v5, false), (v8, false)].size, ∀ j : Fin #[(v5, false), (v8, false)].size,
    i.1 ≠ j.1 → #[(v5, false), (v8, false)][i] ≠ #[(v5, false), (v8, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v5, false), (v8, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c15Nodup :
    ∀ i : Fin #[(v5, false), (v11, false)].size, ∀ j : Fin #[(v5, false), (v11, false)].size,
    i.1 ≠ j.1 → #[(v5, false), (v11, false)][i] ≠ #[(v5, false), (v11, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v5, false), (v11, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c16Nodup :
    ∀ i : Fin #[(v8, false), (v11, false)].size, ∀ j : Fin #[(v8, false), (v11, false)].size,
    i.1 ≠ j.1 → #[(v8, false), (v11, false)][i] ≠ #[(v8, false), (v11, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v8, false), (v11, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c17Nodup :
    ∀ i : Fin #[(v3, false), (v6, false)].size, ∀ j : Fin #[(v3, false), (v6, false)].size,
    i.1 ≠ j.1 → #[(v3, false), (v6, false)][i] ≠ #[(v3, false), (v6, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v3, false), (v6, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c18Nodup :
    ∀ i : Fin #[(v3, false), (v9, false)].size, ∀ j : Fin #[(v3, false), (v9, false)].size,
    i.1 ≠ j.1 → #[(v3, false), (v9, false)][i] ≠ #[(v3, false), (v9, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v3, false), (v9, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c19Nodup :
    ∀ i : Fin #[(v3, false), (v12, false)].size, ∀ j : Fin #[(v3, false), (v12, false)].size,
    i.1 ≠ j.1 → #[(v3, false), (v12, false)][i] ≠ #[(v3, false), (v12, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v3, false), (v12, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c20Nodup :
    ∀ i : Fin #[(v6, false), (v9, false)].size, ∀ j : Fin #[(v6, false), (v9, false)].size,
    i.1 ≠ j.1 → #[(v6, false), (v9, false)][i] ≠ #[(v6, false), (v9, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v6, false), (v9, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c21Nodup :
    ∀ i : Fin #[(v6, false), (v12, false)].size, ∀ j : Fin #[(v6, false), (v12, false)].size,
    i.1 ≠ j.1 → #[(v6, false), (v12, false)][i] ≠ #[(v6, false), (v12, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v6, false), (v12, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]

theorem c22Nodup :
    ∀ i : Fin #[(v9, false), (v12, false)].size, ∀ j : Fin #[(v9, false), (v12, false)].size,
    i.1 ≠ j.1 → #[(v9, false), (v12, false)][i] ≠ #[(v9, false), (v12, false)][j] := by
  intro i j i_ne_j heq
  have hsize : #[(v9, false), (v12, false)].size = 2 := by decide
  simp only [getElem_fin] at heq
  have i_property := i.2
  simp only [hsize] at i_property
  have i_vals := eq_zero_or_one_of_lt_two i_property
  have j_property := j.2
  simp only [hsize] at j_property
  have j_vals := eq_zero_or_one_of_lt_two j_property
  rcases i_vals with hi | hi
  all_goals
    rcases j_vals with hj | hj <;> simp_all (config := { decide := true }) [Array.getElem_eq_data_get, List.get]
