import LeanSAT.Reflect.BoolExpr.Decidable

/--
A version of `BoolExpr α` specialized to `Nat`.

This is purely an optimisation for creating terms that are efficient to typecheck in the kernel.
If you are not sending terms to the kernel, you should use `BoolExpr α` instead.
-/
inductive BoolExprNat
  | literal : Nat → BoolExprNat
  | const : Bool → BoolExprNat
  | not : BoolExprNat → BoolExprNat
  | gate : Gate → BoolExprNat → BoolExprNat → BoolExprNat

namespace BoolExprNat

def eval (f : Nat → Bool) : BoolExprNat → Bool
  | .literal a => f a
  | .const b => b
  | .not x => !eval f x
  | .gate g x y => g.eval (eval f x) (eval f y)

@[simp] theorem eval_literal : eval f (.literal a) = f a := rfl
@[simp] theorem eval_const : eval f (.const b) = b := rfl
@[simp] theorem eval_not : eval f (.not x) = !eval f x := rfl
@[simp] theorem eval_gate : eval f (.gate g x y) = g.eval (eval f x) (eval f y) := rfl

def sat (x : BoolExprNat) (f : Nat → Bool) : Prop := eval f x = true

theorem sat_and {x y : BoolExprNat} {f} (hx : sat x f) (hy : sat y f) : sat (.gate .and x y) f :=
  congr_arg₂ (· && ·) hx hy

theorem sat_true : sat (.const true) f := rfl

def unsat (x : BoolExprNat) : Prop := ∀ f, eval f x = false

def toBoolExpr : BoolExprNat → BoolExpr Nat
  | .literal a => .literal a
  | .const b => .const b
  | .not x => .not (toBoolExpr x)
  | .gate g x y => .gate g (toBoolExpr x) (toBoolExpr y)

def ofBoolExpr : BoolExpr Nat → BoolExprNat
  | .literal a => .literal a
  | .const b => .const b
  | .not x => .not (ofBoolExpr x)
  | .gate g x y => .gate g (ofBoolExpr x) (ofBoolExpr y)

def toString (x : BoolExprNat) : String := x.toBoolExpr.toString

instance : ToString (BoolExprNat) := ⟨toString⟩

@[simp] theorem eval_toBoolExpr (x : BoolExprNat) (f : Nat → Bool) : x.toBoolExpr.eval f = x.eval f := by
  induction x with
  | literal a => rfl
  | const b => rfl
  | not x ih => simp [eval, ih, toBoolExpr]
  | gate g x y ihx ihy => simp [eval, ihx, ihy, toBoolExpr]

theorem sat_iff (x : BoolExprNat) (f : Nat → Bool) : x.sat f ↔ (toBoolExpr x).sat f := by
  simp [sat, BoolExpr.sat]

theorem unsat_iff (x : BoolExprNat) : x.unsat ↔ (toBoolExpr x).unsat := by
  simp [unsat, BoolExpr.unsat]

instance (x : BoolExprNat) : Decidable x.unsat :=
  decidable_of_iff _ (unsat_iff _).symm

end BoolExprNat
