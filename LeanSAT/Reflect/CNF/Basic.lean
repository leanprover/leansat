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

@[simp] theorem not_mem_nil {a : α} : mem a ([] : Clause α) ↔ False := by simp [mem]
@[simp] theorem mem_cons {a : α} : mem a (i :: c : Clause α) ↔ (a = i.1 ∨ mem a c) := by
  rcases i with ⟨b, (_|_)⟩
  · simp [mem, or_assoc]
  · simp [mem]
    rw [or_left_comm]

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

@[simp] theorem not_mem_nil {a : α} : mem a ([] : CNF α) ↔ False := by simp [mem]
@[simp] theorem mem_cons {a : α} {i} {c : CNF α} :
    mem a (i :: c : CNF α) ↔ (Clause.mem a i ∨ mem a c) := by simp [mem]

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
