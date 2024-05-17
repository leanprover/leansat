/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.BoolExpr.Basic

/--
The variable definition used by the bitblaster.
-/
structure BVBit where
  /--
  The width of the BitVec variable.
  -/
  {w : Nat}
  /--
  A numeric identifier for the BitVec variable.
  -/
  var : Nat
  /--
  The which bit we take out of the BitVec variable by getLsb.
  -/
  idx : Fin w
  deriving Hashable, DecidableEq, Repr

instance : ToString BVBit where
  toString b := s!"x{b.var}[{b.idx.val}]"

instance : Inhabited BVBit where
  default :=
    {
        w := 1
        var := 0
        idx := 0
    }

/--
All supported binary operations on `BVExpr`.
-/
inductive BVBinOp where
/--
Bitwise and.
-/
| and
/--
Bitwise or.
-/
| or
/--
Bitwise xor.
-/
| xor
/--
Addition.
-/
| add
/--
Subtractin.
-/
| sub

namespace BVBinOp

def toString : BVBinOp → String
  | and => "&&"
  | or => "||"
  | xor => "^"
  | add => "+"
  | sub => "-"

instance : ToString BVBinOp := ⟨toString⟩

/--
The denotational semantics for `BVBinOp`.
-/
def eval : BVBinOp → (BitVec w → BitVec w → BitVec w)
  | and => (· &&& ·)
  | or => (· ||| ·)
  | xor => (· ^^^ ·)
  | add => (· + ·)
  | sub => (· - ·)

@[simp] theorem eval_and : eval .and = ((· &&& ·) : BitVec w → BitVec w → BitVec w) := by rfl
@[simp] theorem eval_or : eval .or = ((· ||| ·) : BitVec w → BitVec w → BitVec w) := by rfl
@[simp] theorem eval_xor : eval .xor = ((· ^^^ ·) : BitVec w → BitVec w → BitVec w) := by rfl
@[simp] theorem eval_add : eval .add = ((· + ·) : BitVec w → BitVec w → BitVec w) := by rfl
@[simp] theorem eval_sub : eval .sub = ((· - ·) : BitVec w → BitVec w → BitVec w) := by rfl

end BVBinOp

/--
All supported unary operators on `BVExpr`.
-/
inductive BVUnOp where
/--
Bitwise not.
-/
| not
/--
Shifting left by a constant value.

This operation has a dedicated constant representation as shiftLeft can take `Nat` as a shift amount.
We can obviously not bitblast a `Nat` but still want to support the case where the user shifts by a
constant `Nat` value.
-/
| shiftLeftConst (n : Nat)
/--
Shifting right by a constant value.

This operation has a dedicated constant representation as shiftRight can take `Nat` as a shift amount.
We can obviously not bitblast a `Nat` but still want to support the case where the user shifts by a
constant `Nat` value.
-/
| shiftRightConst (n : Nat)
/--
Negation in the sense of 2s complement.
-/
| neg

namespace BVUnOp

def toString : BVUnOp → String
  | not => "~"
  | shiftLeftConst n => s!"<< {n}"
  | shiftRightConst n => s!">> {n}"
  | neg => "-"

instance : ToString BVUnOp := ⟨toString⟩

/--
The denotational semantics for `BVUnOp`.
-/
def eval : BVUnOp → (BitVec w → BitVec w)
  | not => (~~~ ·)
  | shiftLeftConst n => (· <<< n)
  | shiftRightConst n => (· >>> n)
  | neg => (- ·)

@[simp] theorem eval_not : eval .not = ((~~~ ·) : BitVec w → BitVec w) := by rfl

@[simp]
theorem eval_shiftLeftConst : eval (shiftLeftConst n) = ((· <<< n) : BitVec w → BitVec w) := by
  rfl

@[simp]
theorem eval_shiftRightConst : eval (shiftRightConst n) = ((· >>> n) : BitVec w → BitVec w) := by
  rfl

@[simp] theorem eval_neg : eval .neg = ((- ·) : BitVec w → BitVec w) := by rfl

end BVUnOp

/--
All supported expressions involving `BitVec` and operations on them.
-/
inductive BVExpr : Nat → Type where
/--
A `BitVec` variable, referred to through an index.
-/
| var (idx : Nat) : BVExpr w
/--
A constant `BitVec` value.
-/
| const (val : BitVec w) : BVExpr w
| zeroExtend (v : Nat) (expr : BVExpr w) : BVExpr v
/--
A binary operation on two `BVExpr`.
-/
| bin (lhs : BVExpr w) (op : BVBinOp) (rhs : BVExpr w) : BVExpr w
/--
A unary operation on two `BVExpr`.
-/
| un (op : BVUnOp) (operand : BVExpr w) : BVExpr w

namespace BVExpr

def toString : BVExpr w → String
  | .var idx => s!"var{idx}"
  | .const val => ToString.toString val
  | .zeroExtend v expr => s!"(zext {v} {expr.toString})"
  | .bin lhs op rhs => s!"({lhs.toString} {op.toString} {rhs.toString})"
  | .un op operand => s!"({op.toString} {toString operand})"

instance : ToString (BVExpr w) := ⟨toString⟩

/--
Pack a `BitVec` with its width into a single parameter-less structure.
-/
structure PackedBitVec where
  {w : Nat}
  bv: BitVec w

/--
The notion of variable assignments for `BVExpr`.
-/
abbrev Assignment := List PackedBitVec

/--
Obtaining the value of a `BVExpr.var` from an `Assignment`.
-/
def Assignment.getD (assign : Assignment) (idx : Nat) : PackedBitVec :=
  List.getD assign idx ⟨BitVec.zero 0⟩

/--
The denotational semantics for `BVExpr`.
-/
def eval (assign : Assignment) : BVExpr w → BitVec w
  | .var idx =>
    let ⟨bv⟩ := assign.getD idx
    bv.truncate w
  | .const val => val
  | .zeroExtend v expr => BitVec.zeroExtend v (eval assign expr)
  | .bin lhs op rhs => op.eval (eval assign lhs) (eval assign rhs)
  | .un op operand => op.eval (eval assign operand)

@[simp]
theorem eval_var : eval assign ((.var idx) : BVExpr w) = (assign.getD idx).bv.truncate _ := by
  rfl

@[simp]
theorem eval_const : eval assign (.const val) = val := by rfl

@[simp]
theorem eval_zeroExtend : eval assign (.zeroExtend v expr) = BitVec.zeroExtend v (eval assign expr) := by rfl

@[simp]
theorem eval_bin : eval assign (.bin lhs op rhs) = op.eval (lhs.eval assign) (rhs.eval assign) := by
  rfl

@[simp]
theorem eval_un : eval assign (.un op operand) = op.eval (operand.eval assign) := by
  rfl

end BVExpr

/--
Supported binary predicates on `BVExpr`.
-/
inductive BVBinPred where
/--
Equality.
-/
| eq
/--
Unsigned Less Than
-/
| ult
/--
Unsigned Less Than Or Equal
-/
| ule

namespace BVBinPred

def toString : BVBinPred → String
  | eq => "=="
  | ult => "<u"
  | ule => "≤u"

instance : ToString BVBinPred := ⟨toString⟩

/--
The denotational semantics for `BVBinPred`.
-/
def eval : BVBinPred → (BitVec w → BitVec w → Bool)
  | .eq => (· == ·)
  | .ult => BitVec.ult
  | .ule => BitVec.ule

@[simp] theorem eval_eq : eval .eq = ((· == ·) : BitVec w → BitVec w → Bool) := by rfl
@[simp] theorem eval_ult : eval .ult = (BitVec.ult : BitVec w → BitVec w → Bool) := by rfl
@[simp] theorem eval_ule : eval .ule = (BitVec.ule : BitVec w → BitVec w → Bool) := by rfl

end BVBinPred

/--
Supported predicates on `BVExpr`.
-/
inductive BVPred where
/--
A binary predicate on `BVExpr`.
-/
| bin (lhs : BVExpr w) (op : BVBinPred) (rhs : BVExpr w)
/--
Getting a constant LSB from a `BitVec`.
-/
| getLsb (expr : BVExpr w) (idx : Nat)

namespace BVPred

/--
Pack two `BVExpr` of equivalent width into one parameter-less structure.
-/
structure ExprPair where
  {w : Nat}
  lhs : BVExpr w
  rhs : BVExpr w

def toString : BVPred → String
  | bin lhs op rhs => s!"({lhs.toString} {op.toString} {rhs.toString})"
  | getLsb expr idx => s!"{expr.toString}[{idx}]"

instance : ToString BVPred := ⟨toString⟩

/--
The denotational semantics for `BVPred`.
-/
def eval (assign : BVExpr.Assignment) : BVPred → Bool
  | bin lhs op rhs => op.eval (lhs.eval assign) (rhs.eval assign)
  | getLsb expr idx => (expr.eval assign).getLsb idx

@[simp]
theorem eval_bin : eval assign (.bin lhs op rhs) = op.eval (lhs.eval assign) (rhs.eval assign) := by
  rfl

@[simp]
theorem eval_getLsb : eval assign (.getLsb expr idx) = (expr.eval assign).getLsb idx := by
  rfl

end BVPred

/--
Boolean substructure of problems involving predicates on BitVec as atoms.
-/
abbrev BVLogicalExpr := BoolExpr BVPred

namespace BVLogicalExpr

/--
The denotational semantics of boolean problems involving BitVec predicates as toms.
-/
def eval (assign : BVExpr.Assignment) (expr : BVLogicalExpr) : Bool :=
  BoolExpr.eval (·.eval assign) expr

@[simp] theorem eval_literal : eval assign (.literal pred) = pred.eval assign := rfl
@[simp] theorem eval_const : eval assign (.const b) = b := rfl
@[simp] theorem eval_not : eval assign (.not x) = !eval assign x := rfl
@[simp] theorem eval_gate : eval assign (.gate g x y) = g.eval (eval assign x) (eval assign y) := rfl

/--
Definitions of satisfiability on `BVLogicalExpr`.
-/
def sat (x : BVLogicalExpr) (assign : BVExpr.Assignment) : Prop := eval assign x = true

/--
Definitions of unsatisfiability on `BVLogicalExpr`.
-/
def unsat (x : BVLogicalExpr) : Prop := ∀ f, eval f x = false

theorem sat_and {x y : BVLogicalExpr} {assign} (hx : sat x assign) (hy : sat y assign)
    : sat (.gate .and x y) assign := by
  simp only [sat] at *
  simp [hx, hy, Gate.eval]

theorem sat_true : sat (.const true) assign := rfl

end BVLogicalExpr
