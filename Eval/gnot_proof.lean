import LeanSAT.Tactics.BVDecide

set_option sat.timeout 1
open Std (BitVec)
theorem not_sub_thm (x : _root_.BitVec 32) :
    123#32 + x * 4294967295#32 ^^^ 4294967295#32 = x + 4294967172#32 := by
  bv_decide
#exit
theorem not_add_thm (x : _root_.BitVec 32) :
    x + 123#32 ^^^ 4294967295#32 = x * 4294967295#32 + 4294967172#32 := by
  bv_decide

theorem not_or_neg_thm (x x_1 : _root_.BitVec 8) :
    (x_1 * 255#8 ||| x) ^^^ 255#8 = x_1 + 255#8 &&& (x ^^^ 255#8) := by
  bv_decide

