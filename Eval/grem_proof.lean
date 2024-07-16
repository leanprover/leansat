import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem test1_thm (x : _root_.BitVec 32) :
    x + x.sdiv 1#32 * 4294967295#32 = 0#32 := by
  bv_decide

theorem test3_thm (x : _root_.BitVec 32) :
    BitVec.ofNat 32 (x.toNat % 8) = x &&& 7#32 := by
  bv_decide

theorem test7_thm (x : _root_.BitVec 32) :
    x * 8#32 + (x * 8#32).sdiv 4#32 * 4294967292#32 = 0#32 := by
  bv_decide

theorem test8_thm (x : _root_.BitVec 32) :
    x <<< 4 + (x <<< 4).sdiv 8#32 * 4294967288#32 = 0#32 := by
  bv_decide

theorem test12_thm (x : _root_.BitVec 32) :
  (x &&& 4294967292#32) + (x &&& 4294967292#32).sdiv 2#32 * 4294967294#32 = 0#32 := by
  bv_decide
