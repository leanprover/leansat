/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/

namespace Misc

@[simp]
theorem Bool.exists_bool {p : Bool → Prop} : (∃ b, p b) ↔ p false ∨ p true :=
  ⟨fun ⟨b, h⟩ => by cases b; exact Or.inl h; exact Or.inr h,
  fun h => match h with
  | .inl h => ⟨_, h⟩
  | .inr h => ⟨_, h⟩ ⟩

@[simp]
theorem Prod.forall {p : α × β → Prop} : (∀ x, p x) ↔ ∀ a b, p (a, b) :=
  ⟨fun h a b => h (a, b), fun h ⟨a, b⟩ => h a b⟩

@[simp]
theorem Prod.exists {p : α × β → Prop} : (∃ x, p x) ↔ ∃ a b, p (a, b) :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

def List.foldlRecOn {C : β → Sort _} (l : List α) (op : β → α → β) (b : β) (hb : C b)
  (hl : ∀ (b : β) (_ : C b) (a : α) (_ : a ∈ l), C (op b a)) : C (List.foldl op b l) := by
  cases l with
  | nil => exact hb
  | cons hd tl =>
    have IH : (b : β) → C b → ((b : β) → C b → (a : α) → a ∈ tl → C (op b a)) → C (List.foldl op b tl) :=
      foldlRecOn _ _
    refine' IH _ _ _
    · exact hl b hb hd (List.mem_cons_self hd tl)
    · intro y hy x hx
      exact hl y hy x (List.mem_cons_of_mem hd hx)

theorem Array.range_idx {n : Nat} {x : Nat} (h : x < n) : (Array.range n)[x]'(by rw [Array.size_range]; exact h) = x := by
  induction n
  . contradiction
  . next n ih =>
    rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ h with x_lt_n | x_eq_n
    . specialize ih x_lt_n
      simp only [Array.range, Nat.fold, flip, Array.get_push]
      simp only [Array.range, flip] at ih
      split
      . exact ih
      . next x_ge_n =>
        exfalso
        have h_size_range : (Array.range n).size = n := Array.size_range
        simp only [Array.mkEmpty_eq, Array.range, flip] at h_size_range
        simp only [Array.mkEmpty_eq, h_size_range] at x_ge_n
        exact x_ge_n x_lt_n
    . simp only [Array.range, Nat.fold, flip, Array.get_push]
      split
      . next x_lt_n =>
        exfalso
        have h_size_range : (Array.range n).size = n := Array.size_range
        simp only [Array.range, Array.mkEmpty_eq] at h_size_range
        simp only [x_eq_n, Array.mkEmpty_eq, h_size_range, Nat.lt_irrefl] at x_lt_n
      . rw [x_eq_n]

theorem Array.get_modify_at_idx {a : Array α} {i : Nat} (i_in_bounds : i < a.size) (f : α → α) :
  (a.modify i f)[i]'(by rw [Array.size_modify]; exact i_in_bounds) = f (a[i]) := by
  simp only [GetElem.getElem]
  rw [Array.get_modify]
  simp only [↓reduceIte, Array.get_eq_getElem]
  assumption

theorem Array.get_modify_unchanged {a : Array α} {i : Nat} {j : Nat} (j_size : j < a.size)
  (f : α → α) (h : i ≠ j) : (a.modify i f)[j]'(by rw [Array.size_modify]; exact j_size) = a[j] := by
  simp only [GetElem.getElem]
  rw [Array.get_modify]
  simp only [h, ↓reduceIte, Array.get_eq_getElem]
  assumption
