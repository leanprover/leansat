import LeanSAT.Tactics.BVDecide

open Std (BitVec)
set_option sat.timeout 1
theorem p0_scalar_thm (x x_1 : _root_.BitVec 32) :
    x_1 + (x ^^^ 4294967295#32) * 4294967295#32 = x_1 + x + 1#32 := by
  bv_decide

