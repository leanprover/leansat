import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem lshr_exact_thm (x : _root_.BitVec 8) :
    (x <<< 2 + 4#8) >>> 2 = x + 1#8 &&& 63#8 := by
  bv_decide

theorem shl_add_thm (x x_1 : _root_.BitVec 8) :
    (x_1 <<< 2 + x) >>> 2 = x >>> 2 + x_1 &&& 63#8 := by
  bv_decide

theorem negative_and_odd_thm (x : _root_.BitVec 32) :
    (x + x.sdiv 2#32 * 4294967294#32) >>> 31 = x >>> 31 &&& x := by
  bv_decide

