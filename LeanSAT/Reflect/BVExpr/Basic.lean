/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.BoolExpr.Basic

inductive BVBinOp where
| and
| or
| xor

namespace BVBinOp

def toString : BVBinOp → String
  | and => "&&"
  | or => "||"
  | xor => "^"

instance : ToString BVBinOp := ⟨toString⟩

def eval : BVBinOp → (BitVec w → BitVec w → BitVec w)
  | and => (· &&& ·)
  | or => (· ||| ·)
  | xor => (· ^^^ ·)

@[simp] theorem eval_and : eval .and = ((· &&& ·) : BitVec w → BitVec w → BitVec w) := by rfl
@[simp] theorem eval_or : eval .or = ((· ||| ·) : BitVec w → BitVec w → BitVec w) := by rfl
@[simp] theorem eval_xor : eval .xor = ((· ^^^ ·) : BitVec w → BitVec w → BitVec w) := by rfl

end BVBinOp

inductive BVUnOp where
| not

namespace BVUnOp

def toString : BVUnOp → String
  | not => "~"

instance : ToString BVUnOp := ⟨toString⟩

def eval : BVUnOp → (BitVec w → BitVec w)
  | not => (~~~ ·)

@[simp] theorem eval_not : eval .not = ((~~~ ·) : BitVec w → BitVec w) := by rfl

end BVUnOp

inductive BVExpr (w : Nat) where
| var (idx : Nat) : BVExpr w
| const (val : BitVec w) : BVExpr w
| bin (lhs : BVExpr w) (op : BVBinOp) (rhs : BVExpr w) : BVExpr w
| un (op : BVUnOp) (operand : BVExpr w) : BVExpr w

namespace BVExpr

def toString : BVExpr w → String
  | .var idx => s!"var{idx}"
  | .const val => ToString.toString val
  | .bin lhs op rhs => s!"({lhs.toString} {op.toString} {rhs.toString})"
  | .un op operand => s!"({op.toString} {toString operand})"

instance : ToString (BVExpr w) := ⟨toString⟩

def width (_expr : BVExpr w) : Nat := w

structure PackedBitVec where
  {w : Nat}
  bv: BitVec w

abbrev Assignment := List PackedBitVec
def Assignment.getD (assign : Assignment) (idx : Nat) : PackedBitVec :=
  List.getD assign idx ⟨BitVec.zero 0⟩

def eval (assign : Assignment) : BVExpr w → BitVec w
  | .var idx =>
    let ⟨bv⟩ := assign.getD idx
    bv.truncate w
  | .const val => val
  | .bin lhs op rhs => op.eval (eval assign lhs) (eval assign rhs)
  | .un op operand => op.eval (eval assign operand)

@[simp]
theorem eval_var : eval assign ((.var idx) : BVExpr w) = (assign.getD idx).bv.truncate _ := by
  rfl

@[simp]
theorem eval_const : eval assign (.const val) = val := by rfl

@[simp]
theorem eval_bin : eval assign (.bin lhs op rhs) = op.eval (lhs.eval assign) (rhs.eval assign) := by
  rfl

@[simp]
theorem eval_un : eval assign (.un op operand) = op.eval (operand.eval assign) := by
  rfl

end BVExpr

inductive BVBinPred where
| eq
| neq

namespace BVBinPred

def toString : BVBinPred → String
  | eq => "=="
  | neq => "!="

instance : ToString BVBinPred := ⟨toString⟩

def eval : BVBinPred → (BitVec w → BitVec w → Bool)
  | .eq => (· == ·)
  | .neq => (· != ·)

@[simp] theorem eval_eq : eval .eq = ((· == ·) : BitVec w → BitVec w → Bool) := by rfl
@[simp] theorem eval_neq : eval .neq = ((· != ·) : BitVec w → BitVec w → Bool) := by rfl

end BVBinPred

inductive BVPred where
| bin (lhs : BVExpr w) (op : BVBinPred) (rhs : BVExpr w)

namespace BVPred

def toString : BVPred → String
  | bin lhs op rhs => s!"({lhs.toString} {op.toString} {rhs.toString})"

instance : ToString BVPred := ⟨toString⟩

def eval (assign : BVExpr.Assignment) : BVPred → Bool
  | bin lhs op rhs => op.eval (lhs.eval assign) (rhs.eval assign)

@[simp] theorem eval_bin : eval assign (.bin lhs op rhs) = op.eval (lhs.eval assign) (rhs.eval assign) := by rfl

end BVPred

abbrev BVLogicalExpr := BoolExpr BVPred

namespace BVLogicalExpr

def eval (assign : BVExpr.Assignment) (expr : BVLogicalExpr) : Bool :=
  BoolExpr.eval (·.eval assign) expr

@[simp] theorem eval_literal : eval assign (.literal pred) = pred.eval assign := rfl
@[simp] theorem eval_const : eval assign (.const b) = b := rfl
@[simp] theorem eval_not : eval assign (.not x) = !eval assign x := rfl
@[simp] theorem eval_gate : eval assign (.gate g x y) = g.eval (eval assign x) (eval assign y) := rfl

def sat (x : BVLogicalExpr) (assign : BVExpr.Assignment) : Prop := eval assign x = true
def unsat (x : BVLogicalExpr) : Prop := ∀ f, eval f x = false

theorem sat_and {x y : BVLogicalExpr} {assign} (hx : sat x assign) (hy : sat y assign) : sat (.gate .and x y) assign :=
  congr_arg₂ (· && ·) hx hy

theorem sat_true : sat (.const true) assign := rfl

end BVLogicalExpr
