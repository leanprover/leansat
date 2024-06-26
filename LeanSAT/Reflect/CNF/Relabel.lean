/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.CNF.Basic

set_option linter.missingDocs false

namespace List

-- taken from Mathlib, move to Lean
theorem map_congr {f g : α → β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → map f l = map g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    rw [map, map, h₁, map_congr h₂]

end List

namespace CNF

namespace Clause

def relabel (f : α → β) (c : Clause α) : Clause β := c.map (fun (i, n) => (f i, n))

@[simp] theorem eval_relabel {f : α → β} {g : β → Bool} {x : Clause α} :
    (relabel f x).eval g = x.eval (g ∘ f) := by
  induction x <;> simp_all [relabel]

@[simp] theorem relabel_id' : relabel (id : α → α) = id := by funext; simp [relabel]

theorem relabel_congr {x : Clause α} {f g : α → β} (w : ∀ a, mem a x → f a = g a) :
    relabel f x = relabel g x := by
  simp only [relabel]
  rw [List.map_congr]
  intro ⟨i, b⟩ h
  congr
  apply w _ (mem_of h)

-- We need the unapplied equality later.
@[simp] theorem relabel_relabel' : relabel f ∘ relabel g = relabel (f ∘ g) := by
  funext i
  simp only [Function.comp_apply, relabel, List.map_map]
  rfl

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

@[simp] theorem relabel_relabel : relabel f (relabel g x) = relabel (f ∘ g) x := by
  simp only [relabel, List.map_map, Clause.relabel_relabel']

@[simp] theorem relabel_id : relabel id x = x := by simp [relabel]

theorem relabel_congr {x : CNF α} {f g : α → β} (w : ∀ a, mem a x → f a = g a) :
    relabel f x = relabel g x := by
  dsimp only [relabel]
  rw [List.map_congr]
  intro c h
  apply Clause.relabel_congr
  intro a m
  exact w _ (mem_of h m)

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

theorem unsat_relabel_iff {x : CNF α} {f : α → β}
    (w : ∀ {a b}, mem a x → mem b x → f a = f b → a = b) :
    unsat (relabel f x) ↔ unsat x := by
  rcases nonempty_or_impossible x with (⟨⟨a₀⟩⟩ | ⟨n, rfl⟩)
  · refine ⟨fun h => ?_, unsat_relabel f⟩
    have em := Classical.propDecidable
    let g : β → α := fun b =>
      if h : ∃ a, mem a x ∧ f a = b then h.choose else a₀
    have h' := unsat_relabel g h
    suffices w : relabel g (relabel f x) = x by
      rwa [w] at h'
    have : ∀ a, mem a x → g (f a) = a := by
      intro a h
      dsimp [g]
      rw [dif_pos ⟨a, h, rfl⟩]
      apply w _ h
      · exact (Exists.choose_spec (⟨a, h, rfl⟩ : ∃ a', mem a' x ∧ f a' = f a)).2
      · exact (Exists.choose_spec (⟨a, h, rfl⟩ : ∃ a', mem a' x ∧ f a' = f a)).1
    rw [relabel_relabel, relabel_congr, relabel_id]
    exact this
  · cases n <;> simp [unsat, relabel, Clause.relabel, List.replicate_succ]

end CNF
