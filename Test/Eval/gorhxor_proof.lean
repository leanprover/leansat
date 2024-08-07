import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem gorhxor_test5_thm (x x_1 : _root_.BitVec 32) :
  x_1 ^^^ x ||| x_1 ^^^ 4294967295#32 = x_1 &&& x ^^^ 4294967295#32 := by
  bv_decide

theorem gorhxor_test5_commuted_x_y_thm (x x_1 : _root_.BitVec 64) :
  x_1 ^^^ x ||| x ^^^ 18446744073709551615#64 = x_1 &&& x ^^^ 18446744073709551615#64 := by
  bv_decide

theorem gorhxor_test11_thm (x x_1 : _root_.BitVec 32) :
    (x_1 ||| x) &&& (x_1 ^^^ 4294967295#32 ^^^ x) = x_1 &&& x := by
  bv_decide

theorem gorhxor_test12_thm (x x_1 : _root_.BitVec 32) :
    (x_1 ^^^ 4294967295#32 ^^^ x) &&& (x_1 ||| x) = x_1 &&& x := by
  bv_decide

theorem gorhxor_test12_commuted_thm (x x_1 : _root_.BitVec 32) :
    (x_1 ^^^ 4294967295#32 ^^^ x) &&& (x ||| x_1) = x_1 &&& x := by
  bv_decide

theorem gorhxor_test14_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ||| x ^^^ 4294967295#32) ^^^ (x_1 ^^^ 4294967295#32 ||| x) = x_1 ^^^ x := by
  bv_decide

theorem gorhxor_test14_commuted_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ^^^ 4294967295#32 ||| x) ^^^ (x ^^^ 4294967295#32 ||| x_1) = x ^^^ x_1 := by
  bv_decide

theorem gorhxor_test15_thm (x x_1 : _root_.BitVec 32) :
  x_1 &&& (x ^^^ 4294967295#32) ^^^ (x_1 ^^^ 4294967295#32) &&& x = x_1 ^^^ x := by
  bv_decide

theorem gorhxor_test15_commuted_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ^^^ 4294967295#32) &&& x ^^^ (x ^^^ 4294967295#32) &&& x_1 = x ^^^ x_1 := by
  bv_decide

theorem gorhxor_or_and_xor_not_constant_commute0_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ^^^ x) &&& 1#32 ||| x &&& 4294967294#32 = x_1 &&& 1#32 ^^^ x := by
  bv_decide

theorem gorhxor_or_and_xor_not_constant_commute1_thm (x x_1 : _root_.BitVec 9) :
    (x_1 ^^^ x) &&& 42#9 ||| x_1 &&& 469#9 = x &&& 42#9 ^^^ x_1 := by
  bv_decide

theorem gorhxor_not_or_xor_thm (x : _root_.BitVec 8) :
    (x ^^^ 255#8 ||| 7#8) ^^^ 12#8 = x &&& 248#8 ^^^ 243#8 := by
  bv_decide

theorem gorhxor_xor_or_thm (x : _root_.BitVec 8) :
    x ^^^ 32#8 ||| 7#8 = x &&& 248#8 ^^^ 39#8 := by
  bv_decide

theorem gorhxor_xor_or2_thm (x : _root_.BitVec 8) :
    x ^^^ 33#8 ||| 7#8 = x &&& 248#8 ^^^ 39#8 := by
  bv_decide

theorem gorhxor_xor_or_xor_thm (x : _root_.BitVec 8) :
    (x ^^^ 33#8 ||| 7#8) ^^^ 12#8 = x &&& 248#8 ^^^ 43#8 := by
  bv_decide

theorem gorhxor_or_xor_or_thm (x : _root_.BitVec 8) :
    (x ||| 33#8) ^^^ 12#8 ||| 7#8 = x &&& 216#8 ^^^ 47#8 := by
  bv_decide

theorem gorhxor_test17_thm (x x_1 : _root_.BitVec 8) :
  (x_1 ^^^ x ||| x ^^^ 33#8 ^^^ x_1) * (x ^^^ 33#8 ^^^ x_1) =
    (x_1 ^^^ x ||| x ^^^ x_1 ^^^ 33#8) * (x ^^^ x_1 ^^^ 33#8) := by
  bv_decide

theorem gorhxor_test18_thm (x x_1 : _root_.BitVec 8) :
  (x_1 ^^^ 33#8 ^^^ x ||| x ^^^ x_1) * (x_1 ^^^ 33#8 ^^^ x) =
    (x_1 ^^^ x ^^^ 33#8 ||| x ^^^ x_1) * (x_1 ^^^ x ^^^ 33#8) := by
  bv_decide

theorem gorhxor_test19_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ||| x) ^^^ (x_1 ^^^ 4294967295#32 ||| x ^^^ 4294967295#32) = x_1 ^^^ x ^^^ 4294967295#32 := by
  bv_decide

theorem gorhxor_test20_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ||| x) ^^^ (x ^^^ 4294967295#32 ||| x_1 ^^^ 4294967295#32) = x_1 ^^^ x ^^^ 4294967295#32 := by
  bv_decide

theorem gorhxor_test21_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ^^^ 4294967295#32 ||| x ^^^ 4294967295#32) ^^^ (x_1 ||| x) = x_1 ^^^ x ^^^ 4294967295#32 := by
  bv_decide

theorem gorhxor_test22_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ^^^ 4294967295#32 ||| x ^^^ 4294967295#32) ^^^ (x ||| x_1) = x ^^^ x_1 ^^^ 4294967295#32 := by
  bv_decide

theorem gorhxor_test23_thm (x : _root_.BitVec 8) :
    ((x ||| 254#8) ^^^ 13#8 ||| 1#8) ^^^ 12#8 = 255#8 := by
  bv_decide

theorem gorhxor_PR45977_f1_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ||| x) ^^^ 4294967295#32 ||| (x_1 ^^^ 4294967295#32) &&& x = x_1 ^^^ 4294967295#32 := by
  bv_decide

theorem gorhxor_PR45977_f2_thm (x x_1 : _root_.BitVec 32) :
  (x_1 ||| x) ^^^ (x_1 ||| x ^^^ 4294967295#32) = x_1 ^^^ 4294967295#32 := by
  bv_decide

theorem gorhxor_or_not_xor_common_op_commute0_thm (x x_1 x_2 : _root_.BitVec 4) :
  x_2 ^^^ 15#4 ||| x_1 ||| x_2 ^^^ x = x_2 &&& x ^^^ 15#4 ||| x_1 := by
  bv_decide

theorem gorhxor_or_not_xor_common_op_commute2_thm (x x_1 x_2 : _root_.BitVec 8) :
  x_2 ^^^ x_1 ||| (x * 255#8 ||| x_2 ^^^ 255#8) = x_2 &&& x_1 ^^^ 255#8 ||| x * 255#8 := by
  bv_decide

theorem gorhxor_or_not_xor_common_op_commute3_thm (x x_1 x_2 : _root_.BitVec 8) :
  x_2 * 255#8 ||| x_1 ^^^ 255#8 ||| x_1 ^^^ x = x_1 &&& x ^^^ 255#8 ||| x_2 * 255#8 := by
  bv_decide

theorem gorhxor_or_not_xor_common_op_commute5_thm (x x_1 x_2 : _root_.BitVec 8) :
  x_2 ^^^ x_1 ||| (x_1 ^^^ 255#8 ||| x) = x_2 &&& x_1 ^^^ 255#8 ||| x := by
  bv_decide

theorem gorhxor_or_not_xor_common_op_commute6_thm (x x_1 x_2 : _root_.BitVec 8) :
  x_2 ^^^ x_1 ||| (x * 255#8 ||| x_1 ^^^ 255#8) = x_2 &&& x_1 ^^^ 255#8 ||| x * 255#8 := by
  bv_decide

theorem gorhxor_or_not_xor_common_op_commute7_thm (x x_1 x_2 : _root_.BitVec 8) :
  x_2 * 255#8 ||| x_1 ^^^ 255#8 ||| x ^^^ x_1 = x &&& x_1 ^^^ 255#8 ||| x_2 * 255#8 := by
  bv_decide

theorem gorhxor_or_nand_xor_common_op_commute0_thm (x x_1 x_2 : _root_.BitVec 4) :
  x_2 &&& x_1 ^^^ 15#4 ||| x_2 ^^^ x = x_2 &&& x_1 &&& x ^^^ 15#4 := by
  bv_decide

theorem gorhxor_PR75692_1_thm (x : _root_.BitVec 32) :
    x ^^^ 4#32 ||| x ^^^ 4294967291#32 = 4294967295#32 := by
  bv_decide

