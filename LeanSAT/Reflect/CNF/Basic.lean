/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.CNF.ForStd
import Std.Data.Bool
import Std.Data.List.Lemmas
import Std.Tactic.Omega
import Std.Tactic.SimpTrace

-- Lemmas from Mathlib, to move to Lean:
@[simp] theorem exists_or_eq_left (y : α) (p : α → Prop) : ∃ x : α, x = y ∨ p x := ⟨y, .inl rfl⟩
@[simp] theorem exists_or_eq_right (y : α) (p : α → Prop) : ∃ x : α, p x ∨ x = y := ⟨y, .inr rfl⟩
@[simp] theorem exists_or_eq_left' (y : α) (p : α → Prop) : ∃ x : α, y = x ∨ p x := ⟨y, .inl rfl⟩
@[simp] theorem exists_or_eq_right' (y : α) (p : α → Prop) : ∃ x : α, p x ∨ y = x := ⟨y, .inr rfl⟩

theorem List.isEmpty_false_iff_exists_mem (xs : List α) :
    (List.isEmpty xs = false) ↔ ∃ x, x ∈ xs := by
  cases xs <;> simp

set_option linter.missingDocs false

/--
A clause in a CNF.

The literal `(i, b)` is satisfied is the assignment to `i` agrees with `b`.
-/
abbrev CNF.Clause (α : Type) : Type := List (α × Bool)

abbrev CNF (α : Type) : Type := List (CNF.Clause α)

namespace CNF

def Clause.eval (f : α → Bool) (c : Clause α) : Bool := c.any fun (i, n) => f i == n

@[simp] theorem Clause.eval_nil (f : α → Bool) : Clause.eval f [] = false := rfl
@[simp] theorem Clause.eval_succ (f : α → Bool) :
    Clause.eval f (i :: c) = (f i.1 == i.2 || Clause.eval f c) := rfl

def eval (f : α → Bool) (g : CNF α) : Bool := g.all fun c => c.eval f

@[simp] theorem eval_nil (f : α → Bool) : eval f [] = true := rfl
@[simp] theorem eval_succ (f : α → Bool) : eval f (c :: g) = (c.eval f && eval f g) := rfl

@[simp] theorem eval_append (f : α → Bool) (g h : CNF α) :
    eval f (g ++ h) = (eval f g && eval f h) := List.all_append

def sat (g : CNF α) (f : α → Bool) : Prop := eval f g = true
def unsat (g : CNF α) : Prop := ∀ f, eval f g = false

namespace Clause

def mem (a : α) (c : Clause α) : Prop := (a, false) ∈ c ∨ (a, true) ∈ c

instance {a : α} {c : Clause α} [DecidableEq α] : Decidable (mem a c) :=
  inferInstanceAs <| Decidable (_ ∨ _)

@[simp] theorem not_mem_nil {a : α} : mem a ([] : Clause α) ↔ False := by simp [mem]
@[simp] theorem mem_cons {a : α} : mem a (i :: c : Clause α) ↔ (a = i.1 ∨ mem a c) := by
  rcases i with ⟨b, (_|_)⟩
  · simp [mem, or_assoc]
  · simp [mem]
    rw [or_left_comm]

theorem mem_of (h : (a, b) ∈ c) : mem a c := by
  cases b
  · left; exact h
  · right; exact h

theorem eval_congr (f g : α → Bool) (c : Clause α) (w : ∀ i, mem i c → f i = g i) :
    eval f c = eval g c := by
  induction c
  case nil => rfl
  case cons i c ih =>
    simp only [eval_succ]
    rw [ih, w]
    · rcases i with ⟨b, (_|_)⟩ <;> simp [mem]
    · intro j h
      apply w
      rcases h with h | h
      · left
        apply List.mem_cons_of_mem _ h
      · right
        apply List.mem_cons_of_mem _ h

end Clause

def mem (a : α) (g : CNF α) : Prop := ∃ c, c ∈ g ∧ c.mem a

instance {a : α} {g : CNF α} [DecidableEq α] : Decidable (mem a g) :=
  inferInstanceAs <| Decidable (∃ _, _)

instance {g : CNF α} [DecidableEq α] : Decidable (∃ a, mem a g) :=
  decidable_of_iff (g.any fun c => !c.isEmpty) sorry

@[simp] theorem not_mem_nil {a : α} : mem a ([] : CNF α) ↔ False := by simp [mem]
@[simp] theorem mem_cons {a : α} {i} {c : CNF α} :
    mem a (i :: c : CNF α) ↔ (Clause.mem a i ∨ mem a c) := by simp [mem]

theorem mem_of (h : c ∈ g) (w : Clause.mem a c) : mem a g := by
  apply Exists.intro c
  constructor <;> assumption

@[simp] theorem mem_append {a : α} {x y : CNF α} : mem a (x ++ y) ↔ mem a x ∨ mem a y := by
  simp [mem, List.mem_append]
  constructor
  · rintro ⟨c, (mx | my), mc⟩
    · left
      exact ⟨c, mx, mc⟩
    · right
      exact ⟨c, my, mc⟩
  · rintro (⟨c, mx, mc⟩ | ⟨c, my, mc⟩)
    · exact ⟨c, Or.inl mx, mc⟩
    · exact ⟨c, Or.inr my, mc⟩

theorem eval_congr (f g : α → Bool) (x : CNF α) (w : ∀ i, mem i x → f i = g i) :
    eval f x = eval g x := by
  induction x
  case nil => rfl
  case cons c x ih =>
    simp only [eval_succ]
    rw [ih, Clause.eval_congr] <;>
    · intro i h
      apply w
      simp [h]
