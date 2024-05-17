import LeanSAT.Reflect.Tactics.Attr
import Lean.Meta.AppBuilder

/-!
The goal of the simp set provided in this file is to take hypothesis that involve `Bool`
and `BitVec`, both in the `Prop` coerced form (where we write `a ∧ b` and it is turned to
`a = true ∧ b = true`) and the direct form (`(a && b) = true`) and turn all of them into
hypothesis of the form `x = true` where `x` is an expression that is:
1. entirley without the coerced form
2. In the scope of the input grammar of `bv_decide` (TODO: name subject to change)
-/

namespace BVDecide
namespace Normalize

open Lean Meta

/-
This section contains theorems responsible for turning both `Bool` and `BitVec` goals into the
`x = true` normal form expected by `bv_unsat`.
-/
section Normalize

@[bv_normalize]
theorem BitVec.eq_to_beq (a b : BitVec w) : (a = b) = ((a == b) = true) := by
  simp

@[bv_normalize]
theorem BitVec.ne_to_beq (a b : BitVec w) : (a ≠ b) = ((!(a == b)) = true) := by
  simp

theorem Bool.eq_to_beq (a b : Bool) : (a = b) = ((a == b) = true) := by simp

@[bv_normalize]
theorem BitVec.bne_to_beq (a b : BitVec w) : (a != b) = (!(a == b)) := by
  simp [bne]

@[bv_normalize]
theorem Bool.bne_to_beq (a b : Bool) : (a != b) = (!(a == b)) := by
  simp [bne]

simproc [bv_normalize] eqToBEq (((_ : Bool) = (_ : Bool))) := fun e => do
  let_expr Eq _ lhs rhs := e | return .continue
  match_expr rhs with
  | Bool.true => return .continue
  | _ =>
    let beqApp ← mkAppM ``BEq.beq #[lhs, rhs]
    let new := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) beqApp (mkConst ``Bool.true)
    let proof := mkApp2 (mkConst ``Bool.eq_to_beq) lhs rhs
    return .done { expr := new, proof? := some proof }

@[bv_normalize]
theorem Bool.eq_false_to_beq (a : Bool) : (a = false) = ((!a) = true) := by
  simp

@[bv_normalize]
theorem Bool.neg_to_not (a : Bool) : (¬a) = ((!a) = true) := by
  simp

@[bv_normalize]
theorem Bool.ne_to_beq (a b : Bool) : (a ≠ b) = ((!(a == b)) = true) := by
  simp

@[bv_normalize]
theorem Bool.imp_to_or (a b : Bool) : ((a = true) → (b = true)) = (((!a) || b) = true) := by
  revert a b
  decide

@[bv_normalize]
theorem Bool.or_to_or (a b : Bool) : ((a = true) ∨ (b = true)) = ((a || b) = true) := by
  simp

@[bv_normalize]
theorem Bool.and_to_and (a b : Bool) : ((a = true) ∧ (b = true)) = ((a && b) = true) := by
  simp

@[bv_normalize]
theorem Bool.iff_to_or (a b : Bool) : ((a = true) ↔ (b = true)) = (((!a || b) && (!b || a)) = true) := by
  revert a b
  decide

@[bv_normalize]
theorem Bool.eq_false (a : Bool) : ((a = true) = False) = ((!a) = true) := by
  simp

@[bv_normalize]
theorem Bool.decide_eq_true (a : Bool) : (decide (a = true)) = a := by
  simp

@[bv_normalize]
theorem Bool.eq_true_eq_true_eq (x y : Bool) : ((x = true) = (y = true)) = (x = y) :=
  by simp

attribute [bv_normalize] BitVec.getLsb_cast
attribute [bv_normalize] BitVec.msb_eq_getLsb_last
attribute [bv_normalize] BitVec.testBit_toNat

@[bv_normalize]
theorem BitVec.lt_ult (x y : BitVec w) : (x < y) = (BitVec.ult x y = true) := by
  rw [BitVec.ult]
  rw [LT.lt]
  rw [BitVec.instLT]
  simp

@[bv_normalize]
theorem BitVec.gt_ult (x y : BitVec w) : (x > y) = (BitVec.ult y x = true) := by
  simp [GT.gt, BitVec.lt_ult]

@[bv_normalize]
theorem BitVec.le_ule (x y : BitVec w) : (x ≤ y) = (BitVec.ule x y = true) := by
  rw [BitVec.ule]
  rw [LE.le]
  rw [BitVec.instLE]
  simp

@[bv_normalize]
theorem BitVec.ge_ule (x y : BitVec w) : (x ≥ y) = (BitVec.ule y x = true) := by
  simp [GT.gt, BitVec.le_ule]

attribute [bv_normalize] BitVec.natCast_eq_ofNat
attribute [bv_normalize] BitVec.append_eq

end Normalize

/-
This section is tries to do constant folding in the `Prop` fragment that might be of interest for
`bv_normalize`.
-/
section PropConstant

attribute [bv_normalize] not_true
attribute [bv_normalize] and_true
attribute [bv_normalize] true_and
attribute [bv_normalize] or_true
attribute [bv_normalize] true_or

end PropConstant

/-
This section is tries to do constant folding in the `Bool` fragment that might be of interest for
`bv_normalize`.
-/
section BoolConstant

attribute [bv_normalize] Bool.not_true
attribute [bv_normalize] Bool.not_false
attribute [bv_normalize] Bool.or_true
attribute [bv_normalize] Bool.true_or
attribute [bv_normalize] Bool.or_false
attribute [bv_normalize] Bool.false_or
attribute [bv_normalize] Bool.and_true
attribute [bv_normalize] Bool.true_and
attribute [bv_normalize] Bool.and_false
attribute [bv_normalize] Bool.false_and
attribute [bv_normalize] beq_self_eq_true'
attribute [bv_normalize] Bool.not_beq_false
attribute [bv_normalize] Bool.not_beq_true
attribute [bv_normalize] Bool.beq_true
attribute [bv_normalize] Bool.true_beq
attribute [bv_normalize] Bool.beq_false
attribute [bv_normalize] Bool.false_beq
attribute [bv_normalize] Bool.beq_not_self
attribute [bv_normalize] Bool.not_beq_self
attribute [bv_normalize] Bool.beq_self_left
attribute [bv_normalize] Bool.beq_self_right
attribute [bv_normalize] Bool.not_not

end BoolConstant

/-
A large fragment of constant folding is already done with the `seval` simpset. The following
only contains additional lemmas that are of interest
-/

section BitVecConstant

attribute [bv_normalize] BitVec.add_zero
attribute [bv_normalize] BitVec.zero_add
attribute [bv_normalize] BitVec.neg_zero
attribute [bv_normalize] BitVec.sub_self
attribute [bv_normalize] BitVec.sub_zero
attribute [bv_normalize] BitVec.zeroExtend_eq
attribute [bv_normalize] BitVec.zeroExtend_zero
attribute [bv_normalize] BitVec.shiftLeft_shiftLeft
attribute [bv_normalize] BitVec.shiftRight_shiftRight
attribute [bv_normalize] BitVec.getLsb_zero
attribute [bv_normalize] BitVec.getLsb_zero_length
attribute [bv_normalize] BitVec.getLsb_concat_zero

end BitVecConstant

end Normalize

end BVDecide

syntax (name := bvNormalizeSyntax) "bv_normalize" : tactic

macro_rules
| `(tactic| bv_normalize) =>
   `(tactic|
      apply Classical.byContradiction;
      intro;
      simp only [bv_normalize, seval] at *
   )
