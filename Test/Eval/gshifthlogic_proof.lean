import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem shl_and_thm (x x_1 : _root_.BitVec 8) :
    (x_1 <<< 3 &&& x) <<< 2 = x_1 <<< 5 &&& x <<< 2 := by
  bv_decide

theorem shl_or_thm (x x_1 : _root_.BitVec 16) :
  (x_1 + x_1.sdiv 42#16 * 65494#16 ||| x <<< 5) <<< 7 = x <<< 12 ||| (x_1 + x_1.sdiv 42#16 * 65494#16) <<< 7 := by
  bv_decide

theorem shl_xor_thm (x x_1 : _root_.BitVec 32) :
    (x_1 <<< 5 ^^^ x) <<< 7 = x_1 <<< 12 ^^^ x <<< 7 := by
  bv_decide

theorem lshr_and_thm (x x_1 : _root_.BitVec 64) :
  (x_1 + x_1.sdiv 42#64 * 18446744073709551574#64 &&& x >>> 5) >>> 7 =
    x >>> 12 &&& (x_1 + x_1.sdiv 42#64 * 18446744073709551574#64) >>> 7 := by
  bv_decide

theorem ashr_xor_thm (x x_1 : _root_.BitVec 32) :
  (x_1 + x_1.sdiv 42#32 * 4294967254#32 ^^^ x.sshiftRight 5).sshiftRight 7 =
    x.sshiftRight 12 ^^^ (x_1 + x_1.sdiv 42#32 * 4294967254#32).sshiftRight 7 := by
  bv_decide

theorem ashr_overshift_xor_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ^^^ x.sshiftRight 15).sshiftRight 17 = (x.sshiftRight 15 ^^^ x_1).sshiftRight 17 := by
  bv_decide

theorem shl_add_thm (x x_1 : _root_.BitVec 8) :
    (x_1 <<< 3 + x) <<< 2 = x_1 <<< 5 + x <<< 2 := by
  bv_decide

theorem shl_sub_thm (x x_1 : _root_.BitVec 8) :
    (x_1 <<< 3 + x * 255#8) <<< 2 = 255#8 * x <<< 2 + x_1 <<< 5 := by
  bv_decide

theorem shl_sub_no_commute_thm (x x_1 : _root_.BitVec 8) :
    (x_1 + x <<< 3 * 255#8) <<< 2 = 255#8 * x <<< 5 + x_1 <<< 2 := by
  bv_decide

