import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem t9_c0_c2_thm (x : _root_.BitVec 8) :
    42#8 + x * 255#8 + 232#8 = x * 255#8 + 18#8 := by
  bv_decide

