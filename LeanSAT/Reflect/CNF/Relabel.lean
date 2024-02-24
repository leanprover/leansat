/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.CNF.Basic

set_option linter.missingDocs false

@[simp] theorem _root_.List.map_replicate :
    (List.replicate n a).map f = List.replicate n (f a) := by
  induction n <;> simp_all

namespace CNF

namespace Clause

def relabel (f : α → β) (c : Clause α) : Clause β := c.map (fun (i, n) => (f i, n))

@[simp] theorem eval_relabel {f : α → β} {g : β → Bool} {x : Clause α} :
    (relabel f x).eval g = x.eval (g ∘ f) := by
  induction x <;> simp_all [relabel]

end Clause

/-! ### Relabelling

It is convenient to be able to construct a CNF using a more complicated literal type,
but eventually we need to embed in `Nat`.
-/

def relabel (f : α → β) (g : CNF α) : CNF β := g.map (Clause.relabel f)

@[simp] theorem eval_relabel (f : α → β) (g : β → Bool) (x : CNF α) :
    (relabel f x).eval g = x.eval (g ∘ f) := by
  induction x <;> simp_all [relabel]

@[simp] theorem relabel_append : relabel f (g ++ h) = relabel f g ++ relabel f h :=
  List.map_append _ _ _

theorem sat_relabel (h : sat x (g ∘ f)) : sat (relabel f x) g := by
  simp_all [sat]

theorem unsat_relabel {x : CNF α} (f : α → β) (h : unsat x) : unsat (relabel f x) := by
  simp_all [unsat]

theorem nonempty_or_impossible (x : CNF α) : Nonempty α ∨ ∃ n, x = List.replicate n [] := by
  induction x with
  | nil => exact Or.inr ⟨0, rfl⟩
  | cons c x ih => match c with
    | [] => cases ih with
      | inl h => left; exact h
      | inr h =>
        obtain ⟨n, rfl⟩ := h
        right
        exact ⟨n + 1, rfl⟩
    | ⟨a, b⟩ :: c => exact Or.inl ⟨a⟩

theorem unsat_relabel_iff {x : CNF α} {f : α → β} (w : ∀ a b, f a = f b → a = b) :
    unsat (relabel f x) ↔ unsat x := by
  rcases nonempty_or_impossible x with (⟨⟨a₀⟩⟩ | ⟨n, rfl⟩)
  · refine ⟨fun h => ?_, unsat_relabel f⟩
    have em := Classical.propDecidable
    let g : β → α := fun b =>
      if h : ∃ a, f a = b then h.choose else a₀
    have h' := unsat_relabel g h
    suffices w : relabel g (relabel f x) = x by
      rwa [w] at h'
    simp only [relabel, List.map_map]
    suffices w : Clause.relabel _ ∘ Clause.relabel _ = id by
      rw [w, List.map_id]
    funext c
    simp only [Function.comp_apply, id_eq, Clause.relabel, List.map_map]
    suffices w : _ ∘ _ = id by
      rw [w, List.map_id]
    funext ⟨a, b⟩
    simp only [Function.comp_apply, exists_apply_eq_apply, ↓reduceDite, id_eq]
    congr
    apply w
    exact Exists.choose_spec (⟨a, rfl⟩ : ∃ a', f a' = f a)
  · cases n <;> simp [unsat, relabel, Clause.relabel]

end CNF
