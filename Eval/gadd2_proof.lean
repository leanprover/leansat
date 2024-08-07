import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem test2_thm (x : _root_.BitVec 32) :
    (x &&& 7#32) + (x &&& 32#32) = x &&& 39#32 := by
  bv_decide

theorem test3_thm (x : _root_.BitVec 32) :
    (x &&& 128#32) + x >>> 30 = x &&& 128#32 ||| x >>> 30 := by
  bv_decide

theorem test4_thm (x : _root_.BitVec 32) :
    x * 2#32 = x <<< 1 := by
  bv_decide

set_option sat.timeout 1
theorem test9_thm (x : _root_.BitVec 16) :
    x * 2#16 + x * 32767#16 = x * 32769#16 := by
  bv_decide

#exit

theorem test10_thm (x x_1 : _root_.BitVec 32) :
  x_1 + 1#32 + ((x.sshiftRight 3 ||| 2863311530#32) ^^^ 1431655765#32) =
    x_1 + (x.sshiftRight 3 &&& 1431655765#32) * 4294967295#32 := by
  bv_decide

theorem test11_thm (x x_1 : _root_.BitVec 32) :
  x_1 + 1#32 + ((x ||| 2863311530#32) ^^^ 1431655765#32) = x_1 + (x &&& 1431655765#32) * 4294967295#32 := by
  bv_decide

theorem test12_thm (x x_1 : _root_.BitVec 32) :
  x_1 + 1#32 + ((x ||| 2863311530#32) ^^^ 1431655765#32) = x_1 + (x &&& 1431655765#32) * 4294967295#32 := by
  bv_decide

theorem test13_thm (x x_1 : _root_.BitVec 32) :
  x_1 + 1#32 + ((x ||| 2863311529#32) ^^^ 1431655766#32) = x_1 + (x &&& 1431655766#32) * 4294967295#32 := by
  bv_decide

theorem test14_thm (x x_1 : _root_.BitVec 32) :
  x_1 + 1#32 + ((x ||| 2863311529#32) ^^^ 1431655766#32) = x_1 + (x &&& 1431655766#32) * 4294967295#32 := by
  bv_decide

theorem test15_thm (x x_1 : _root_.BitVec 32) :
  x_1 + 1#32 + (x &&& 2863311529#32 ^^^ 2863311529#32) = x_1 + (x ||| 1431655766#32) * 4294967295#32 := by
  bv_decide

theorem test16_thm (x x_1 : _root_.BitVec 32) :
  x_1 + 1#32 + (x &&& 2863311529#32 ^^^ 2863311529#32) = x_1 + (x ||| 1431655766#32) * 4294967295#32 := by
  bv_decide

theorem test17_thm (x x_1 : _root_.BitVec 32) :
  (x_1 &&& 2863311530#32 ^^^ 2863311531#32) + x = x + (x_1 ||| 1431655765#32) * 4294967295#32 := by
  bv_decide

theorem test18_thm (x x_1 : _root_.BitVec 32) :
  x_1 + 1#32 + (x &&& 2863311530#32 ^^^ 2863311530#32) = x_1 + (x ||| 1431655765#32) * 4294967295#32 := by
  bv_decide

theorem mul_add_to_mul_1_thm (x : _root_.BitVec 16) : 
    x + x * 8#16 = x * 9#16 := by
  bv_decide

theorem mul_add_to_mul_2_thm (x : _root_.BitVec 16) : 
    x + x * 8#16 = x * 9#16 := by
  bv_decide

theorem mul_add_to_mul_3_thm (x : _root_.BitVec 16) : 
    x * 2#16 + x * 3#16 = x * 5#16 := by
  bv_decide

theorem mul_add_to_mul_4_thm (x : _root_.BitVec 16) : 
    x * 2#16 + x * 7#16 = x * 9#16 := by
  bv_decide

theorem mul_add_to_mul_5_thm (x : _root_.BitVec 16) : 
    x * 3#16 + x * 7#16 = x * 10#16 := by
  bv_decide

theorem mul_add_to_mul_6_thm (x x_1 : _root_.BitVec 32) : 
    x_1 * x + x_1 * x * 5#32 = x_1 * x * 6#32 := by
  bv_decide

theorem mul_add_to_mul_7_thm (x : _root_.BitVec 16) : 
    x + x * 32767#16 = x <<< 15 := by
  bv_decide

theorem mul_add_to_mul_8_thm (x : _root_.BitVec 16) : 
    x * 16383#16 + x * 16384#16 = x * 32767#16 := by
  bv_decide

theorem mul_add_to_mul_9_thm (x : _root_.BitVec 16) : 
    x * 32768#16 = x <<< 15 := by
  bv_decide

theorem add_or_and_thm (x x_1 : _root_.BitVec 32) : 
    (x_1 ||| x) + (x_1 &&& x) = x_1 + x := by
  bv_decide

theorem add_or_and_commutative_thm (x x_1 : _root_.BitVec 32) : 
    (x_1 ||| x) + (x &&& x_1) = x_1 + x := by
  bv_decide

theorem add_and_or_commutative_thm (x x_1 : _root_.BitVec 32) : 
    (x_1 &&& x) + (x ||| x_1) = x + x_1 := by
  bv_decide

theorem add_nsw_or_and_thm (x x_1 : _root_.BitVec 32) : 
    (x_1 ||| x) + (x_1 &&& x) = x_1 + x := by
  bv_decide

theorem add_nuw_or_and_thm (x x_1 : _root_.BitVec 32) : 
    (x_1 ||| x) + (x_1 &&& x) = x_1 + x := by
  bv_decide

theorem add_nuw_nsw_or_and_thm (x x_1 : _root_.BitVec 32) : 
    (x_1 ||| x) + (x_1 &&& x) = x_1 + x := by
  bv_decide

theorem add_undemanded_low_bits_thm (x : _root_.BitVec 32) : 
    ((x ||| 15#32) + 1616#32) >>> 4 = (1616#32 + x) >>> 4 := by
  bv_decide

theorem sub_undemanded_low_bits_thm (x : _root_.BitVec 32) : 
    ((x ||| 15#32) + 4294965680#32) >>> 4 = (4294965680#32 + x) >>> 4 := by
  bv_decide

