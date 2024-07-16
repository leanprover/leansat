import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem gxor2_test2_thm (x : _root_.BitVec 32) :
    (x &&& 32#32) + 145#32 ^^^ 153#32 = x &&& 32#32 ||| 8#32 := by
  bv_decide

theorem gxor2_test3_thm (x : _root_.BitVec 32) :
    (x ||| 145#32) &&& 177#32 ^^^ 153#32 = x &&& 32#32 ||| 8#32 := by
  bv_decide

theorem gxor2_test5_thm (x : _root_.BitVec 32) :
    (x ^^^ 1234#32) >>> 8 ^^^ 1#32 = x >>> 8 ^^^ 5#32 := by
  bv_decide

theorem gxor2_test6_thm (x : _root_.BitVec 32) :
    (x ^^^ 1234#32) >>> 16 = x >>> 16 := by
  bv_decide

theorem gxor2_test7_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ||| x) ^^^ (x_1 ^^^ 4294967295#32) = x ^^^ 4294967295#32 ||| x_1 := by
  bv_decide

theorem gxor2_test8_thm (x x_1 : _root_.BitVec 32) :
  x_1 ^^^ 4294967295#32 ^^^ (x_1 ||| x) = x ^^^ 4294967295#32 ||| x_1 := by
  bv_decide

theorem gxor2_test12_thm (x x_1 : _root_.BitVec 32) :
  x_1 &&& (x ^^^ 4294967295#32) ^^^ (x_1 ^^^ 4294967295#32) = x_1 &&& x ^^^ 4294967295#32 := by
  bv_decide

theorem gxor2_test12commuted_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ^^^ 4294967295#32) &&& x ^^^ (x ^^^ 4294967295#32) = x &&& x_1 ^^^ 4294967295#32 := by
  bv_decide

theorem gxor2_test13_thm (x x_1 : _root_.BitVec 32) :
  x_1 ^^^ 4294967295#32 ^^^ x_1 &&& (x ^^^ 4294967295#32) = x_1 &&& x ^^^ 4294967295#32 := by
  bv_decide

theorem gxor2_test13commuted_thm (x x_1 : _root_.BitVec 32) :
  x_1 ^^^ 4294967295#32 ^^^ (x ^^^ 4294967295#32) &&& x_1 = x_1 &&& x ^^^ 4294967295#32 := by
  bv_decide

theorem gxor2_xor_or_xor_common_op_commute1_thm (x x_1 x_2 : _root_.BitVec 32) :
  x_2 ^^^ x_1 ^^^ (x_2 ||| x) = (x_2 ^^^ 4294967295#32) &&& x ^^^ x_1 := by
  bv_decide

theorem gxor2_xor_or_xor_common_op_commute2_thm (x x_1 x_2 : _root_.BitVec 32) :
  x_2 ^^^ x_1 ^^^ (x_1 ||| x) = (x_1 ^^^ 4294967295#32) &&& x ^^^ x_2 := by
  bv_decide

theorem gxor2_xor_or_xor_common_op_commute3_thm (x x_1 x_2 : _root_.BitVec 32) :
  x_2 ^^^ x_1 ^^^ (x ||| x_2) = (x_2 ^^^ 4294967295#32) &&& x ^^^ x_1 := by
  bv_decide

theorem gxor2_xor_or_xor_common_op_commute4_thm (x x_1 x_2 : _root_.BitVec 32) :
  x_2 ^^^ x_1 ^^^ (x ||| x_1) = (x_1 ^^^ 4294967295#32) &&& x ^^^ x_2 := by
  bv_decide

theorem gxor2_xor_or_xor_common_op_commute5_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ||| x_1) ^^^ (x_2 ^^^ x) = (x_2 ^^^ 4294967295#32) &&& x_1 ^^^ x := by
  bv_decide

theorem gxor2_xor_or_xor_common_op_commute6_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ||| x_1) ^^^ (x ^^^ x_2) = (x_2 ^^^ 4294967295#32) &&& x_1 ^^^ x := by
  bv_decide

theorem gxor2_xor_or_xor_common_op_commute7_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ||| x_1) ^^^ (x_1 ^^^ x) = (x_1 ^^^ 4294967295#32) &&& x_2 ^^^ x := by
  bv_decide

theorem gxor2_xor_or_xor_common_op_commute8_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ||| x_1) ^^^ (x ^^^ x_1) = (x_1 ^^^ 4294967295#32) &&& x_2 ^^^ x := by
  bv_decide

theorem gxor2_test15_thm (x x_1 : _root_.BitVec 8) :
  ((x_1 ^^^ x) &&& (x ^^^ 33#8 ^^^ x_1)) * (x ^^^ 33#8 ^^^ x_1) =
    ((x_1 ^^^ x) &&& (x ^^^ x_1 ^^^ 33#8)) * (x ^^^ x_1 ^^^ 33#8) := by
  bv_decide

theorem gxor2_test16_thm (x x_1 : _root_.BitVec 8) :
  ((x_1 ^^^ 33#8 ^^^ x) &&& (x ^^^ x_1)) * (x_1 ^^^ 33#8 ^^^ x) =
    ((x_1 ^^^ x ^^^ 33#8) &&& (x ^^^ x_1)) * (x_1 ^^^ x ^^^ 33#8) := by
  bv_decide

theorem gxor2_not_xor_to_or_not1_thm (x x_1 x_2 : _root_.BitVec 3) :
  x_2 &&& x_1 ^^^ (x ||| x_1) ^^^ 7#3 = x_2 &&& x_1 ||| (x ||| x_1) ^^^ 7#3 := by
  bv_decide

theorem gxor2_not_xor_to_or_not2_thm (x x_1 x_2 : _root_.BitVec 3) :
  x_2 &&& x_1 ^^^ (x_1 ||| x) ^^^ 7#3 = x_2 &&& x_1 ||| (x_1 ||| x) ^^^ 7#3 := by
  bv_decide

theorem gxor2_not_xor_to_or_not3_thm (x x_1 x_2 : _root_.BitVec 3) :
  x_2 &&& x_1 ^^^ (x_2 ||| x) ^^^ 7#3 = x_2 &&& x_1 ||| (x_2 ||| x) ^^^ 7#3 := by
  bv_decide

theorem gxor2_not_xor_to_or_not4_thm (x x_1 x_2 : _root_.BitVec 3) :
  x_2 &&& x_1 ^^^ (x ||| x_2) ^^^ 7#3 = x_2 &&& x_1 ||| (x ||| x_2) ^^^ 7#3 := by
  bv_decide

theorem gxor2_xor_notand_to_or_not1_thm (x x_1 x_2 : _root_.BitVec 3) :
  x_2 &&& x_1 ^^^ 7#3 ^^^ (x ||| x_1) = x_2 &&& x_1 ||| (x ||| x_1) ^^^ 7#3 := by
  bv_decide

theorem gxor2_xor_notand_to_or_not2_thm (x x_1 x_2 : _root_.BitVec 3) :
  x_2 &&& x_1 ^^^ 7#3 ^^^ (x_1 ||| x) = x_2 &&& x_1 ||| (x_1 ||| x) ^^^ 7#3 := by
  bv_decide

theorem gxor2_xor_notand_to_or_not3_thm (x x_1 x_2 : _root_.BitVec 3) :
  x_2 &&& x_1 ^^^ 7#3 ^^^ (x_2 ||| x) = x_2 &&& x_1 ||| (x_2 ||| x) ^^^ 7#3 := by
  bv_decide

theorem gxor2_xor_notand_to_or_not4_thm (x x_1 x_2 : _root_.BitVec 3) :
  x_2 &&& x_1 ^^^ 7#3 ^^^ (x ||| x_2) = x_2 &&& x_1 ||| (x ||| x_2) ^^^ 7#3 := by
  bv_decide
