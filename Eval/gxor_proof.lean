import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem test5_thm (x : _root_.BitVec 32) :
    (x ||| 123#32) ^^^ 123#32 = x &&& 4294967172#32 := by
  bv_decide

theorem test7_thm (x x_1 : _root_.BitVec 32) :
    x_1 &&& 7#32 ^^^ x &&& 128#32 = x_1 &&& 7#32 ||| x &&& 128#32 := by
  bv_decide

theorem test10_thm (x : _root_.BitVec 8) :
    x &&& 3#8 ^^^ 4#8 = x &&& 3#8 ||| 4#8 := by
  bv_decide

theorem test11_thm (x : _root_.BitVec 8) :
    (x ||| 12#8) ^^^ 4#8 = x &&& 243#8 ||| 8#8 := by
  bv_decide

set_option sat.timeout 1
theorem test18_thm (x : _root_.BitVec 32) :
    123#32 + (x ^^^ 4294967295#32) * 4294967295#32 = x + 124#32 := by
  bv_decide

theorem test25_thm (x x_1 : _root_.BitVec 32) :
    (x_1 ^^^ 4294967295#32) &&& x ^^^ x = x_1 &&& x := by
  bv_decide

theorem test28_thm (x : _root_.BitVec 32) :
    x + 2147483649#32 ^^^ 2147483648#32 = x + 1#32 := by
  bv_decide

theorem test28_sub_thm (x : _root_.BitVec 32) :
  2147483649#32 + x * 4294967295#32 ^^^ 2147483648#32 = x * 4294967295#32 + 1#32 := by
  bv_decide

theorem or_or_xor_thm (x x_1 x_2 : _root_.BitVec 4) :
  (x_2 ||| x_1) ^^^ (x_2 ||| x) = (x_1 ^^^ x) &&& (x_2 ^^^ 15#4) := by
  bv_decide

theorem or_or_xor_commute1_thm (x x_1 x_2 : _root_.BitVec 4) :
  (x_2 ||| x_1) ^^^ (x_1 ||| x) = (x_2 ^^^ x) &&& (x_1 ^^^ 15#4) := by
  bv_decide

theorem or_or_xor_commute2_thm (x x_1 x_2 : _root_.BitVec 4) :
  (x_2 ||| x_1) ^^^ (x ||| x_2) = (x_1 ^^^ x) &&& (x_2 ^^^ 15#4) := by
  bv_decide

theorem not_is_canonical_thm (x x_1 : _root_.BitVec 32) :
  ((x_1 ^^^ 1073741823#32) + x) <<< 2 = (x + (x_1 ^^^ 4294967295#32)) <<< 2 := by
  bv_decide

theorem not_shl_thm (x : _root_.BitVec 8) :
    x <<< 7 ^^^ 128#8 = (x ^^^ 255#8) <<< 7 := by
  bv_decide

theorem not_lshr_thm (x : _root_.BitVec 8) :
    x >>> 5 ^^^ 7#8 = (x ^^^ 255#8) >>> 5 := by
  bv_decide

theorem ashr_not_thm (x : _root_.BitVec 8) :
    (x ^^^ 255#8).sshiftRight 5 = x.sshiftRight 5 ^^^ 255#8 := by
  bv_decide

theorem PR96857_xor_with_noundef_thm (x x_1 x_2 : _root_.BitVec 4) :
  x_2 &&& x_1 ^^^ (x_2 ^^^ 15#4) &&& x = x_2 &&& x_1 ||| (x_2 ^^^ 15#4) &&& x := by
  bv_decide

theorem PR96857_xor_without_noundef_thm (x x_1 x_2 : _root_.BitVec 4) :
  x_2 &&& x_1 ^^^ (x_2 ^^^ 15#4) &&& x = x_2 &&& x_1 ||| (x_2 ^^^ 15#4) &&& x := by
  bv_decide

