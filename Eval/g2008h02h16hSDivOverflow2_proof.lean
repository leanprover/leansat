import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem i_thm (x : _root_.BitVec 8) :
    (x.sdiv 253#8).sdiv 253#8 = x.sdiv 9#8 := by
  bv_decide

