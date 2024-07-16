import LeanSAT.Tactics.BVDecide

open Std (BitVec)

theorem sub_from_constant_of_add_with_constant_thm (x : _root_.BitVec 8) :
    11#8 + x * 255#8 + 214#8 = x * 255#8 + 225#8 := by
  bv_decide

theorem negate_xor_thm (x : _root_.BitVec 4) :
    (x ^^^ 5#4) * 15#4 = (x ^^^ 10#4) + 1#4 := by
  bv_decide

theorem negate_sdiv_thm (x : _root_.BitVec 8) :
    x.sdiv 42#8 * 255#8 = x.sdiv 214#8 := by
  bv_decide

theorem negate_ashr_thm (x : _root_.BitVec 8) :
    x.sshiftRight 7 * 255#8 = x >>> 7 := by
  bv_decide

theorem negate_lshr_thm (x : _root_.BitVec 8) :
    x >>> 7 * 255#8 = x.sshiftRight 7 := by
  bv_decide

theorem negation_of_increment_via_or_with_no_common_bits_set_thm (x : _root_.BitVec 8) : 
    (x <<< 1 ||| 1#8) * 255#8 = x <<< 1 ^^^ 255#8 := by
  bv_decide

theorem negate_add_with_single_negatible_operand_depth2_thm (x : _root_.BitVec 8) : 
    21#8 * x * 255#8 = x * 235#8 := by
  bv_decide

