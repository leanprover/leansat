import LeanSAT.Reflect.Tactics.Attr

namespace BVDecide
namespace Normalize

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

end Constant

end Normalize
end BVDecide

