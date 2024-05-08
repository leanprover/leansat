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

@[bv_normalize]
theorem BitVec.eq_to_beq (a b : BitVec w) : (a = b) = ((a == b) = true) := by
  simp

@[bv_normalize]
theorem BitVec.ne_to_beq (a b : BitVec w) : (a ≠ b) = ((!(a == b)) = true) := by
  simp

theorem Bool.eq_to_beq (a b : Bool) : (a = b) = ((a == b) = true) := by simp

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
theorem not_true : (¬True) = (false = true) := by
  simp

attribute [bv_normalize] and_true
attribute [bv_normalize] true_and
attribute [bv_normalize] or_true
attribute [bv_normalize] true_or

end Normalize
end BVDecide

syntax (name := bvNormalizeSyntax) "bv_normalize" : tactic

macro_rules
| `(tactic| bv_normalize) =>
   `(tactic|
      apply Classical.byContradiction;
      intro;
      simp only [bv_normalize] at *
   )
