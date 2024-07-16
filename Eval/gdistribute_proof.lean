import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem factorize_thm (x : _root_.BitVec 32) :
    (x ||| 1#32) &&& (x ||| 2#32) = x := by
  bv_decide

set_option sat.timeout 1
theorem factorize2_thm (x : _root_.BitVec 32) :
    3#32 * x + x * 4294967294#32 = x := by
  bv_decide
#exit
theorem factorize4_thm (x x_1 : _root_.BitVec 32) :
    x_1 <<< 1 * x + x * x_1 * 4294967295#32 = x * x_1 := by
  bv_decide

theorem factorize5_thm (x x_1 : _root_.BitVec 32) :
    x_1 * 2#32 * x + x_1 * x * 4294967295#32 = x_1 * x := by
  bv_decide

theorem expand_thm (x : _root_.BitVec 32) :
    (x &&& 1#32 ||| 2#32) &&& 1#32 = x &&& 1#32 := by
  bv_decide

