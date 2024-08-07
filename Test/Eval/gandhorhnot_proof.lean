import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem and_to_xor1_thm (x x_1 : _root_.BitVec 32) :
    (x_1 ||| x) &&& (x_1 &&& x ^^^ 4294967295#32) = x_1 ^^^ x := by
  bv_decide

theorem and_to_xor2_thm (x x_1 : _root_.BitVec 32) :
    (x_1 &&& x ^^^ 4294967295#32) &&& (x_1 ||| x) = x_1 ^^^ x := by
  bv_decide

theorem and_to_xor3_thm (x x_1 : _root_.BitVec 32) :
    (x_1 ||| x) &&& (x &&& x_1 ^^^ 4294967295#32) = x_1 ^^^ x := by
  bv_decide

theorem and_to_xor4_thm (x x_1 : _root_.BitVec 32) :
    (x_1 &&& x ^^^ 4294967295#32) &&& (x ||| x_1) = x ^^^ x_1 := by
  bv_decide

theorem or_to_nxor1_thm (x x_1 : _root_.BitVec 32) :
  x_1 &&& x ||| (x_1 ||| x) ^^^ 4294967295#32 = x_1 ^^^ x ^^^ 4294967295#32 := by
  bv_decide

theorem or_to_nxor2_thm (x x_1 : _root_.BitVec 32) :
  x_1 &&& x ||| (x ||| x_1) ^^^ 4294967295#32 = x_1 ^^^ x ^^^ 4294967295#32 := by
  bv_decide

theorem or_to_nxor3_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ||| x) ^^^ 4294967295#32 ||| x_1 &&& x = x_1 ^^^ x ^^^ 4294967295#32 := by
  bv_decide

theorem or_to_nxor4_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ||| x) ^^^ 4294967295#32 ||| x &&& x_1 = x ^^^ x_1 ^^^ 4294967295#32 := by
  bv_decide

theorem simplify_or_common_op_commute0_thm (x x_1 x_2 : _root_.BitVec 4) :
    x_2 &&& x_1 &&& x ^^^ 15#4 ||| x_2 = 15#4 := by
  bv_decide

theorem simplify_or_common_op_commute1_thm (x x_1 x_2 : _root_.BitVec 4) :
    x_2 &&& x_1 &&& x ^^^ 15#4 ||| x_1 = 15#4 := by
  bv_decide

theorem simplify_and_common_op_commute1_thm (x x_1 x_2 : _root_.BitVec 4) :
    ((x_2 ||| x_1 ||| x) ^^^ 15#4) &&& x_1 = 0#4 := by
  bv_decide

