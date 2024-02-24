/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.CNF.ForStd
import Std.Data.Bool
import Std.Tactic.Omega
import Std.Tactic.SimpTrace

set_option linter.missingDocs false

abbrev CNF.Clause (α : Type) : Type := List (α × Bool)

abbrev CNF (α : Type) : Type := List (CNF.Clause α)

namespace CNF

def Clause.eval (f : α → Bool) (c : Clause α) : Bool := c.any fun (i, n) => xor n (f i)

@[simp] theorem Clause.eval_nil (f : α → Bool) : Clause.eval f [] = false := rfl
@[simp] theorem Clause.eval_succ (f : α → Bool) :
    Clause.eval f (i :: c) = ((xor i.2 (f i.1)) || Clause.eval f c) := rfl

def eval (f : α → Bool) (g : CNF α) : Bool := g.all fun c => c.eval f

@[simp] theorem eval_nil (f : α → Bool) : eval f [] = true := rfl
@[simp] theorem eval_succ (f : α → Bool) : eval f (c :: g) = (c.eval f && eval f g) := rfl

@[simp] theorem eval_append (f : α → Bool) (g h : CNF α) :
    eval f (g ++ h) = (eval f g && eval f h) := List.all_append

def sat (g : CNF α) (f : α → Bool) : Prop := eval f g = true
def unsat (g : CNF α) : Prop := ∀ f, eval f g = false

namespace Clause

def mem (a : α) (c : Clause α) : Prop := (a, false) ∈ c ∨ (a, true) ∈ c

instance : Membership α (Clause α) := ⟨mem⟩

@[simp] theorem not_mem_nil {a : α} : a ∈ ([] : Clause α) ↔ False := sorry
@[simp] theorem mem_cons {a : α} : (a ∈ (i :: c : Clause α)) ↔ (a = i.1 ∨ a ∈ c) := sorry

theorem eval_congr (f g : α → Bool) (c : Clause α) (w : ∀ i, i ∈ c → f i = g i) :
    eval f c = eval g c := by
  induction c
  case nil => rfl
  case cons i c ih =>
    simp only [eval_succ]
    rw [ih, w]
    · sorry
    · intro j h
      apply w
      sorry

end Clause

def mem (a : α) (g : CNF α) : Prop := ∃ c, c ∈ g ∧ c.mem a

instance : Membership α (CNF α) := ⟨mem⟩

@[simp] theorem not_mem_nil {a : α} : a ∈ ([] : CNF α) ↔ False := sorry
@[simp] theorem mem_cons {a : α} {i} {c : CNF α} : (a ∈ (i :: c : CNF α)) ↔ (a ∈ i ∨ a ∈ c) := sorry

@[simp] theorem mem_append {a : α} {x y : CNF α} : a ∈ x ++ y ↔ a ∈ x ∨ a ∈ y := sorry

theorem eval_congr (f g : α → Bool) (x : CNF α) (w : ∀ i, i ∈ x → f i = g i) :
    eval f x = eval g x := by
  induction x
  case nil => rfl
  case cons c x ih =>
    simp only [eval_succ]
    rw [ih, Clause.eval_congr]
    · sorry
    · sorry
