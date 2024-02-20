/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.Util.Misc

open Misc

namespace List

/-- List of keys from a list of key-value pairs -/
def keys : List (α × β) → List α := map Prod.fst

def Nodupkeys (l : List (α × β)) : Prop := (l.map (fun x => x.1)).Nodup

theorem nodupkeys_iff_pairwise {l} : l.Nodupkeys ↔
  List.Pairwise (fun s s' : α × β => s.1 ≠ s'.1) l := List.pairwise_map

theorem nodupkeys_eq_of_fst_eq {l : List (α × β)} (nd : l.Nodupkeys)
  {s s' : α × β} (h : s ∈ l) (h' : s' ∈ l) : s.1 = s'.1 → s = s' := by
  intro keys_eq
  have goal_rw : (s = s') = (s.1 = s'.1 ∧ s.2 = s'.2) := by
    have s_rw : s = (s.1, s.2) := rfl
    have s'_rw : s' = (s'.1, s'.2) := rfl
    rw [s_rw, s'_rw]
    simp only [Prod.mk.injEq]
  rw [goal_rw]
  constructor
  . exact keys_eq
  . induction l with
    | nil => exact False.elim $ List.not_mem_nil s h
    | cons hd tl ih =>
      rw [List.Nodupkeys, List.Nodup, List.Pairwise_iff] at nd
      simp only [List.map_eq_nil, ne_eq] at nd
      rcases nd with l_eq_nil | ⟨a, l', nd⟩
      . exact False.elim l_eq_nil
      . rw [List.Nodupkeys, List.Nodup] at ih
        rcases nd with ⟨nd1, nd2, nd3⟩
        rw [List.map_cons] at nd3
        simp only [List.cons.injEq] at nd3
        rcases nd3 with ⟨hd_fst_eq_a, nd3⟩
        rw [← nd3] at nd2
        specialize ih nd2
        rw [List.mem_cons] at h h'
        rcases h with s_eq_hd | s_in_tl
        . rcases h' with s'_eq_hd | s'_in_tl
          . rw [s_eq_hd, s'_eq_hd]
          . rw [← nd3, ← hd_fst_eq_a, ← s_eq_hd] at nd1
            specialize nd1 s'.1
            simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right,
              forall_exists_index] at nd1
            specialize nd1 s'.2 s'_in_tl
            exfalso
            exact nd1 keys_eq
        . rcases h' with s'_eq_hd | s'_in_tl
          . rw [← nd3, ← hd_fst_eq_a, ← s'_eq_hd] at nd1
            specialize nd1 s.1
            simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right,
              forall_exists_index] at nd1
            specialize nd1 s.2 s_in_tl
            exfalso
            exact nd1 keys_eq.symm
          . exact ih s_in_tl s'_in_tl

theorem nodupkeys_eq_of_mk_mem {a : α} {b b' : β} {l : List (α × β)}
  (nd : l.Nodupkeys) (h : (a, b) ∈ l) (h' : (a, b') ∈ l) : b = b' := by
  have goal := nodupkeys_eq_of_fst_eq nd h h' rfl
  simp only [Prod.mk.injEq, true_and] at goal
  exact goal
