/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Tactics.Attr
import LeanSAT.Tactics.Normalize.Bool
import LeanSAT.Tactics.Normalize.Canonicalize

namespace BVDecide
namespace Normalize

open Lean Meta

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

@[bv_normalize]
theorem BitVec.OfNat_reduce (n : Nat) : OfNat.ofNat n = BitVec.ofNat w n := by
  rfl

@[bv_normalize]
theorem BitVec.ofNatLt_reduce (n : Nat) (h) : BitVec.ofNatLt n h = BitVec.ofNat w n := by
  simp [BitVec.ofNatLt, BitVec.ofNat, Fin.ofNat', Nat.mod_eq_of_lt h]

end Reduce

section Constant

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
attribute [bv_normalize] BitVec.mul_one
attribute [bv_normalize] BitVec.one_mul

/--
The bitblaster for multiplication introduces symbolic branches over the right hand side.
If we have an expression of the form `c * x` where `c` is constant we should change it to `x * c`
such that these symbolic branches get constant folded by the AIG framework.
-/
simproc [bv_normalize] mulConst ((_ : BitVec _) * (_ : BitVec _)) := fun e => do
  let_expr HMul.hMul _ _ _ _ lhs rhs := e | return .continue
  let some ⟨width, _⟩ ← Lean.Meta.getBitVecValue? lhs | return .continue
  let new ← mkAppM ``HMul.hMul #[rhs, lhs]
  let proof := mkApp3 (mkConst ``BitVec.mul_comm) (toExpr width) lhs rhs
  return .done { expr := new, proof? := some proof }

end Constant

@[bv_normalize]
theorem BitVec.zero_and (a : BitVec w) : 0#w &&& a = 0#w := by
  ext
  simp

@[bv_normalize]
theorem BitVec.and_zero (a : BitVec w) : a &&& 0#w = 0#w := by
  ext
  simp

@[bv_normalize]
theorem BitVec.and_ones (a : BitVec w) : (-1#w) &&& a = a := by
  ext
  simp [BitVec.negOne_eq_allOnes]

@[bv_normalize]
theorem BitVec.ones_and (a : BitVec w) : a &&& (-1#w) = a := by
  ext
  simp [BitVec.negOne_eq_allOnes]

@[bv_normalize]
theorem BitVec.and_self (a : BitVec w) : a &&& a = a := by
  ext
  simp

@[bv_normalize]
theorem BitVec.and_contra (a : BitVec w) : a &&& ~~~a = 0#w := by
  ext
  simp

@[bv_normalize]
theorem BitVec.and_contra' (a : BitVec w) : ~~~a &&& a = 0#w := by
  ext
  simp

@[bv_normalize]
theorem BitVec.add_not (a : BitVec w) : a + ~~~a = (-1#w) := by
  ext
  simp [BitVec.negOne_eq_allOnes]

@[bv_normalize]
theorem BitVec.not_add (a : BitVec w) : ~~~a + a = (-1#w) := by
  rw [BitVec.add_comm]
  rw [BitVec.add_not]

@[bv_normalize]
theorem BitVec.add_neg (a : BitVec w) : a + (-a) = 0#w := by
  rw [← BitVec.sub_toAdd]
  rw [BitVec.sub_self]

@[bv_normalize]
theorem BitVec.neg_add (a : BitVec w) : (-a) + a = 0#w := by
  rw [BitVec.add_comm]
  rw [BitVec.add_neg]

@[bv_normalize]
theorem BitVec.zero_sshiftRight : BitVec.sshiftRight 0#w a = 0#w := by
  ext
  simp [BitVec.getLsb_sshiftRight]

@[bv_normalize]
theorem BitVec.sshiftRight_zero : BitVec.sshiftRight a 0 = a := by
  ext
  simp [BitVec.getLsb_sshiftRight]

@[bv_normalize]
theorem BitVec.mul_zero (a : BitVec w) : a * 0#w = 0#w := by
  simp [bv_toNat]

@[bv_normalize]
theorem BitVec.zero_mul (a : BitVec w) : 0#w * a = 0#w := by
  simp [bv_toNat]

@[bv_normalize]
theorem BitVec.not_not (a : BitVec w) : ~~~(~~~a) = a := by
  ext
  simp

@[bv_normalize]
theorem BitVec.shiftLeft_zero (n : BitVec w) : n <<< 0#w' = n := by
  ext i
  simp only [(· <<< ·)]
  simp

@[bv_normalize]
theorem BitVec.shiftLeft_zero' (n : BitVec w) : n <<< 0 = n := by
  ext i
  simp

@[bv_normalize]
theorem BitVec.zero_shiftLeft (n : Nat) : 0#w <<< n = 0#w := by
  ext
  simp

@[bv_normalize]
theorem BitVec.zero_shiftRight (n : Nat) : 0#w >>> n = 0#w := by
  ext
  simp

@[bv_normalize]
theorem BitVec.shiftRight_zero (n : BitVec w) : n >>> 0#w' = n := by
  ext i
  simp only [(· >>> ·)]
  simp

@[bv_normalize]
theorem BitVec.shiftRight_zero' (n : BitVec w) : n >>> 0 = n := by
  ext i
  simp

theorem BitVec.zero_lt_iff_zero_neq (a : BitVec w) : (0#w < a) ↔ (0#w ≠ a) := by
  constructor <;>
    simp_all only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.zero_mod, ne_eq, BitVec.toNat_eq] <;>
    omega

@[bv_normalize]
theorem BitVec.zero_ult' (a : BitVec w) : (BitVec.ult 0#w a) = (0#w != a) := by
  have := BitVec.zero_lt_iff_zero_neq a
  rw [BitVec.lt_ult] at this
  match h:BitVec.ult 0#w a with
  | true => simp_all
  | false => simp_all

theorem BitVec.max_ult (a : BitVec w) : ¬ ((-1#w) < a) := by
rcases w with rfl | w
· simp [bv_toNat]
· simp only [BitVec.lt_def, BitVec.toNat_neg, BitVec.toNat_ofNat, Nat.not_lt]
  rw[Nat.mod_eq_of_lt (a := 1) (by simp)];
  rw [Nat.mod_eq_of_lt]
  · omega
  · apply Nat.sub_one_lt_of_le (Nat.pow_pos (by omega)) (Nat.le_refl ..)

@[bv_normalize]
theorem BitVec.max_ult' (a : BitVec w) : (BitVec.ult (-1#w) a) = false := by
  have := BitVec.max_ult a
  rw [BitVec.lt_ult] at this
  simp [this]

attribute [bv_normalize] BitVec.replicate_zero_eq

end Normalize
end BVDecide

