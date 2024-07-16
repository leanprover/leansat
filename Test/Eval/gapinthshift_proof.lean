import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem test6_thm (x : _root_.BitVec 55) :
    x <<< 1 * 3#55 = x * 6#55 := by
  bv_decide

theorem test6a_thm (x : _root_.BitVec 55) :
    (x * 3#55) <<< 1 = x * 6#55 := by
  bv_decide

theorem test9_thm (x : _root_.BitVec 17) :
    x <<< 16 >>> 16 = x &&& 1#17 := by
  bv_decide

