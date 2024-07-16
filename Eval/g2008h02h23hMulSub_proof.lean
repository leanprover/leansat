import LeanSAT.Tactics.BVDecide

-- Currently times out
set_option sat.timeout 1
open Std (BitVec)
theorem test_thm (x : _root_.BitVec 26) :
    x * 2885#26 + x * 67105980#26 = x := by
  bv_decide

