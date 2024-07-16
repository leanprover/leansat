import LeanSAT.Tactics.BVDecide

set_option sat.timeout 1
open Std (BitVec)
theorem t0_thm (x x_1 : _root_.BitVec 32) :
    (x_1 ^^^ 4294967295#32) + x + 1#32 = x + x_1 * 4294967295#32 := by
  bv_decide
