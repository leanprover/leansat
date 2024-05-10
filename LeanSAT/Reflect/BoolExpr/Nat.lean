import LeanSAT.Reflect.BoolExpr.Decidable
import Batteries.Data.Array.Lemmas

namespace List

theorem length_ofFn_go {f : Fin n → α} {i j : Nat} {h} : length (ofFn.go f i j h) = i := by
  induction i generalizing j with
  | zero => simp[ofFn.go]
  | succ n ih =>
    dsimp [ofFn.go]
    rw [ih]

@[simp]
theorem length_ofFn {f : Fin k → α} : (List.ofFn f).length = k := by
  simp [ofFn, length_ofFn_go]

@[simp] theorem get_Array_data : (Array.data x).get i = x.get (Fin.cast (by simp) i) := by
  rfl

theorem get_ofFn_go {f : Fin k → α} {i j k : Nat} {h} {hk} :
    (List.ofFn.go f i j h).get ⟨k, hk⟩ = f ⟨j + k, by simp[length_ofFn_go] at hk; omega⟩ := by
  let i+1 := i
  cases k with
  | zero => dsimp [ofFn.go]
  | succ k =>
    dsimp [ofFn.go]
    rw [get_ofFn_go]
    congr 2
    simp_arith
termination_by i

@[simp]
theorem get_ofFn {f : Fin k → α} {i : Fin (List.ofFn f).length} :
    (List.ofFn f).get i = f (Fin.cast (by simp) i) := by
  rcases i with ⟨i, hi⟩
  simp [ofFn, get_ofFn_go]

theorem getD_ofFn {f : Fin k → α} : (List.ofFn f).getD i d = if h : i < k then f ⟨i, h⟩ else d := by
  simp [List.getD]
  if h : i < (ofFn f).length then
    rw [get?_eq_get h]
    rw [length_ofFn] at h
    rw [dif_pos h]
    simp
  else
    rw [get?_eq_none.mpr (by simpa using h)]
    rw [length_ofFn] at h
    rw [dif_neg h]
    rfl

end List

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

def eval (f : List Bool) : BoolExprNat → Bool
  | .literal a => f.getD a false
  | .const b => b
  | .not x => !eval f x
  | .gate g x y => g.eval (eval f x) (eval f y)

@[simp] theorem eval_literal : eval f (.literal a) = f.getD a false := rfl
@[simp] theorem eval_const : eval f (.const b) = b := rfl
@[simp] theorem eval_not : eval f (.not x) = !eval f x := rfl
@[simp] theorem eval_gate : eval f (.gate g x y) = g.eval (eval f x) (eval f y) := rfl

def sat (x : BoolExprNat) (f : List Bool) : Prop := eval f x = true

theorem sat_and {x y : BoolExprNat} {f} (hx : sat x f) (hy : sat y f) : sat (.gate .and x y) f := by
  simp only [sat] at *
  simp [hx, hy, Gate.eval]

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

@[simp] theorem eval_toBoolExpr (x : BoolExprNat) (f : List Bool) :
    x.toBoolExpr.eval (f.getD · false) = x.eval f := by
  induction x with
  | literal a => rfl
  | const b => rfl
  | not x ih => simp [eval, ih, toBoolExpr]
  | gate g x y ihx ihy => simp [eval, ihx, ihy, toBoolExpr]

@[simp] theorem eval_ofFn (x : BoolExprNat) (f : Fin k → Bool) :
    x.eval (List.ofFn f) = x.toBoolExpr.eval fun i => if h : i < k then f ⟨i, h⟩ else false  := by
  match x with
  | literal a => simp [toBoolExpr, List.getD_ofFn]
  | const b => rfl
  | not x => simp [eval, toBoolExpr, eval_ofFn]
  | gate g x y => simp [eval, toBoolExpr, eval_ofFn]

@[simp] theorem eval_if (f : List Bool) :
    (toBoolExpr x).eval (fun i => i < (toBoolExpr x).vars && f.getD i false) =
      x.eval f := by
  match x with
  | literal a => simp [toBoolExpr]
  | const b => rfl
  | not x => simp [toBoolExpr, eval_if]
  | gate g x y =>
    simp [toBoolExpr]
    rw [BoolExpr.eval_congr, eval_if f, BoolExpr.eval_congr, eval_if f]
    · intro i h
      simp only [h, decide_True, Bool.true_and, Bool.and_iff_right_iff_imp, decide_eq_true_eq]
      omega
    · intro i h
      simp only [h, decide_True, Bool.true_and, Bool.and_iff_right_iff_imp, decide_eq_true_eq]
      omega

theorem sat_iff (x : BoolExprNat) (f : List Bool) :
    x.sat f ↔ (toBoolExpr x).sat (f.getD · false) := by
  simp [sat, BoolExpr.sat]

theorem unsat_iff (x : BoolExprNat) : x.unsat ↔ (toBoolExpr x).unsat := by
  rw [← BoolExpr.attach_unsat]
  simp only [unsat, BoolExpr.unsat]
  constructor
  · intro h f
    specialize h (List.ofFn f)
    simpa using h
  · intro h f
    specialize h (f.getD · false)
    simpa using h

instance (x : BoolExprNat) : Decidable x.unsat :=
  decidable_of_iff _ (unsat_iff _).symm

end BoolExprNat
