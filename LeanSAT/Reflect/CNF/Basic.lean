/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.CNF.ForStd
import Std.Data.Bool

set_option linter.missingDocs false

abbrev CNF.Clause (α : Type) : Type := List (α × Bool)

abbrev CNF (α : Type) : Type := List (CNF.Clause α)

namespace CNF

def Clause.eval (f : α → Bool) (c : Clause α) : Bool := c.any fun (i, n) => xor n (f i)

@[simp] theorem Clause.eval_nil (f : α → Bool) : Clause.eval f [] = false := rfl
@[simp] theorem Clause.eval_succ (f : α → Bool) :
    Clause.eval f ((a, b) :: c) = ((xor b (f a)) || Clause.eval f c) := rfl

def eval (f : α → Bool) (g : CNF α) : Bool := g.all fun c => c.eval f

@[simp] theorem eval_nil (f : α → Bool) : eval f [] = true := rfl
@[simp] theorem eval_succ (f : α → Bool) : eval f (c :: g) = (c.eval f && eval f g) := rfl

@[simp] theorem eval_append (f : α → Bool) (g h : CNF α) :
    eval f (g ++ h) = (eval f g && eval f h) := List.all_append

def sat (g : CNF α) (f : α → Bool) : Prop := eval f g = true
def unsat (g : CNF α) : Prop := ∀ f, eval f g = false

end CNF
