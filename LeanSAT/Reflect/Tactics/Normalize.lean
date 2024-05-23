import LeanSAT.Reflect.Tactics.Attr
import Lean.Meta.AppBuilder
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.FalseOrByContra

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

attribute [bv_normalize] BitVec.natCast_eq_ofNat
attribute [bv_normalize] BitVec.append_eq
attribute [bv_normalize] BitVec.and_eq
attribute [bv_normalize] BitVec.or_eq
attribute [bv_normalize] BitVec.xor_eq
attribute [bv_normalize] BitVec.not_eq
attribute [bv_normalize] BitVec.shiftLeft_eq
attribute [bv_normalize] BitVec.ushiftRight_eq
attribute [bv_normalize] BitVec.add_eq
attribute [bv_normalize] BitVec.sub_eq
attribute [bv_normalize] BitVec.neg_eq

@[bv_normalize]
theorem Bool.and_eq_and (x y : Bool) : x.and y = (x && y) := by
  rfl

@[bv_normalize]
theorem Bool.or_eq_or (x y : Bool) : x.or y = (x || y) := by
  rfl

@[bv_normalize]
theorem Bool.no_eq_not (x : Bool) : x.not = !x := by
  rfl


end Normalize


/-
This section contains theorems that Bitwzula uses to reduce the surface level QF_BV theory to more
minimal one:
https://github.com/bitwuzla/bitwuzla/blob/229c0fa35bfbdcae7189558f98911a24909a7f04/src/rewrite/rewriter.cpp#L979
-/
section Reduce

attribute [bv_normalize] BitVec.neg_eq_not_add

attribute [bv_normalize] BitVec.sub_toAdd

@[bv_normalize]
theorem BitVec.le_ult (x y : BitVec w) : (x ≤ y) = ¬(x > y) := by
  simp only [(· ≤ ·), (· > ·), (· < ·)]
  simp
attribute [bv_normalize] BitVec.ule_eq_not_ult

attribute [bv_normalize] gt_iff_lt
attribute [bv_normalize] ge_iff_le

@[bv_normalize]
theorem BitVec.truncate_eq_zeroExtend (x : BitVec w) : x.truncate n = x.zeroExtend n := by
  rfl

attribute [bv_normalize] BitVec.msb_eq_getLsb_last
attribute [bv_normalize] BitVec.slt_eq_ult
attribute [bv_normalize] BitVec.sle_eq_not_slt

end Reduce

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
attribute [bv_normalize] BitVec.reduceShiftLeftShiftLeft
attribute [bv_normalize] BitVec.reduceShiftRightShiftRight
attribute [bv_normalize] BitVec.getLsb_zero
attribute [bv_normalize] BitVec.getLsb_zero_length
attribute [bv_normalize] BitVec.getLsb_concat_zero

end BitVecConstant

open Lean Elab Meta Tactic

structure Result where
  goal : MVarId
  stats : Simp.Stats

def _root_.Lean.MVarId.bvNormalize (g : MVarId) : MetaM (Option Result) := do
  withTraceNode `bv (fun _ => return "Normalizing goal") do
    -- Contradiction proof
    let g ← g.falseOrByContra

    -- Normalization by simp
    let bvThms ← bvNormalizeExt.getTheorems
    let bvSimprocs ← bvNormalizeSimprocExt.getSimprocs
    let sevalThms ← getSEvalTheorems
    let sevalSimprocs ← Simp.getSEvalSimprocs

    let simpCtx : Simp.Context := {
      simpTheorems := #[bvThms, sevalThms]
      congrTheorems := (← getSimpCongrTheorems)
    }

    let hyps ← g.getNondepPropHyps
    -- TODO: Think about whether having a discharger might be interesting
    let ⟨result?, stats⟩ ← simpGoal g
      (ctx := simpCtx)
      (simprocs := #[bvSimprocs, sevalSimprocs])
      (fvarIdsToSimp := hyps)
    let some (_, g) := result? | return none
    return some ⟨g, stats⟩

end Normalize
end BVDecide

