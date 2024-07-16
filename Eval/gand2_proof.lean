import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem test9_thm (x : _root_.BitVec 64) :
    x * 18446744073709551615#64 &&& 1#64 = x &&& 1#64 := by
  bv_decide

set_option sat.timeout 1
theorem test10_thm (x : _root_.BitVec 64) :
  x * 18446744073709551615#64 + (x * 18446744073709551615#64 &&& 1#64) =
    18446744073709551615#64 * (x &&& 18446744073709551614#64) := by
  bv_decide

theorem test11_thm (x x_1 : _root_.BitVec 32) :
  x_1 <<< 8 * (x_1 <<< 8 + x &&& 128#32) = x_1 <<< 8 * (x &&& 128#32) := by
  bv_decide

theorem test12_thm (x x_1 : _root_.BitVec 32) :
  x <<< 8 * (x_1 + x <<< 8 &&& 128#32) = x <<< 8 * (x_1 &&& 128#32) := by
  bv_decide

theorem test13_thm (x x_1 : _root_.BitVec 32) :
  x <<< 8 * (x_1 + x <<< 8 * 4294967295#32 &&& 128#32) = x <<< 8 * (x_1 &&& 128#32) := by
  bv_decide

theorem test14_thm (x x_1 : _root_.BitVec 32) :
  x_1 <<< 8 * (x_1 <<< 8 + x * 4294967295#32 &&& 128#32) = x_1 <<< 8 * (x * 4294967295#32 &&& 128#32) := by
  bv_decide
