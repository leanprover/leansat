import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem shl_and_and_thm (x x_1 : _root_.BitVec 8) :
    x_1 <<< 4 &&& (x <<< 4 &&& 88#8) = (x &&& x_1) <<< 4 &&& 80#8 := by
  bv_decide

theorem shl_and_and_fail_thm (x x_1 : _root_.BitVec 8) :
  x_1 <<< 4 &&& (x <<< 5 &&& 88#8) = x_1 <<< 4 &&& (x <<< 5 &&& 64#8) := by
  bv_decide

theorem shl_add_add_thm (x x_1 : _root_.BitVec 8) :
    x_1 <<< 2 + x <<< 2 + 48#8 = 48#8 + (x + x_1) <<< 2 := by
  bv_decide

theorem shl_and_xor_thm (x x_1 : _root_.BitVec 8) :
    x_1 <<< 1 ^^^ x <<< 1 &&& 20#8 = (x &&& 10#8 ^^^ x_1) <<< 1 := by
  bv_decide

theorem shl_and_add_thm (x x_1 : _root_.BitVec 8) :
    x_1 <<< 1 + (x <<< 1 &&& 119#8) = ((x &&& 59#8) + x_1) <<< 1 := by
  bv_decide

theorem lshr_or_and_thm (x x_1 : _root_.BitVec 8) :
  (x_1 >>> 5 ||| 198#8) &&& x >>> 5 = ((x_1 ||| 192#8) &&& x) >>> 5 := by
  bv_decide

theorem lshr_xor_or_good_mask_thm (x x_1 : _root_.BitVec 8) :
    x_1 >>> 4 ||| x >>> 4 ^^^ 48#8 = (x ||| x_1) >>> 4 ||| 48#8 := by
  bv_decide

theorem shl_add_and_thm (x x_1 : _root_.BitVec 8) :
    x_1 <<< 1 &&& x <<< 1 + 123#8 = (x + 61#8 &&& x_1) <<< 1 := by
  bv_decide
