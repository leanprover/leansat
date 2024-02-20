/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.BoolExpr.Basic
import LeanSAT.Reflect.Fin

set_option linter.missingDocs false

namespace BoolExpr

def map (f : α → β) : BoolExpr α → BoolExpr β
  | .literal a => .literal (f a)
  | .const b => .const b
  | .not x   => .not (map f x)
  | .gate g x y => .gate g (map f x) (map f y)

@[simp] theorem eval_map (f : α → β) (g : β → Bool) : (map f x).eval g = eval (g ∘ f) x := by
  cases x <;> simp_all [map, eval, eval_map]

def vars : BoolExpr Nat → Nat
  | .literal i => i + 1
  | .const _ => 0
  | .not x => vars x
  | .gate _ x y => max (vars x) (vars y)

@[simp] theorem vars_literal : vars (.literal i) = i + 1 := rfl
@[simp] theorem vars_const : vars (.const b) = 0 := rfl
@[simp] theorem vars_not : vars (.not x) = vars x := rfl
@[simp] theorem vars_gate : vars (.gate g x y ) = max (vars x) (vars y) := rfl

theorem eval_congr (f g : Nat → Bool) (w : ∀ i, i < vars x → f i = g i) : eval f x = eval g x := by
  match x with
  | .literal i => dsimp [eval]; apply w; simp
  | .const b => rfl
  | .not x =>
    dsimp [eval]
    rw [eval_congr f g]
    exact w
  | .gate h x y =>
    dsimp [eval]
    rw [eval_congr f g, eval_congr f g]
    exact fun i h => w i (Nat.lt_of_lt_of_le h (Nat.le_max_right _ _))
    exact fun i h => w i (Nat.lt_of_lt_of_le h (Nat.le_max_left _ _))

def attach (x : BoolExpr Nat) : BoolExpr (Fin x.vars) :=
  go x x.vars (Nat.le_refl _)
where
  go : (x : BoolExpr Nat) → (k : Nat) → x.vars ≤ k → BoolExpr (Fin k)
    | .literal i, _, h  => .literal ⟨i, h⟩
    | .const b, _, _ => .const b
    | .not x, k, h => .not (go x k h)
    | .gate g x y, k, h =>
        .gate g (go x k (Nat.le_trans (Nat.le_max_left _ _) h))
          (go y k (Nat.le_trans (Nat.le_max_right _ _) h))

@[simp] theorem attach_not : attach (.not x) = .not (attach x) := rfl

def forget : BoolExpr (Fin w) → BoolExpr Nat := map Fin.val

theorem eval_forget (x : BoolExpr (Fin w)) (f : Nat → Bool) :
    (forget x).eval f = x.eval fun i : Fin w => f i :=
  eval_map _ _

theorem map_fin_val_attach_go : map Fin.val (attach.go x k h) = x := by
  cases x <;> simp [attach.go, map, map_fin_val_attach_go]

theorem forget_attach : forget (attach x) = x :=
  map_fin_val_attach_go

theorem eval_attach (x : BoolExpr Nat) (f : Fin x.vars → Bool) :
    (attach x).eval f = x.eval fun i => if h : i < x.vars then f ⟨i, h⟩ else false := by
  generalize h : (fun i => if h : i < x.vars then f ⟨i, h⟩ else false) = f'
  obtain rfl := show f = fun i : Fin _ => f' i by subst h; simp
  rw [← eval_forget, forget_attach]

theorem attach_unsat : (attach x).unsat ↔ x.unsat :=
  ⟨fun h f => by
    specialize h fun i => f i
    rw [eval_attach] at h
    rw [← h]
    apply eval_congr
    simp_all,
  fun h f => by
    specialize h fun i => if h : i < x.vars then f ⟨i, h⟩ else false
    rw [eval_attach]
    exact h⟩

instance (x : BoolExpr (Fin n)) : Decidable x.unsat :=
  inferInstanceAs <| Decidable (∀ f, eval f x = false)

instance (x : BoolExpr Nat) : Decidable x.unsat :=
  decidable_of_iff _ attach_unsat

end BoolExpr
