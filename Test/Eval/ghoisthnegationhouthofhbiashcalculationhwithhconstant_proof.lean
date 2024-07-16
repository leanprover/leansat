import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem withconstnat_t0_thm (x : _root_.BitVec 8) :
    (x &&& 42#8) + x * 255#8 = (x &&& 213#8) * 255#8 := by
  bv_decide

theorem withconstant_n5_thm (x : _root_.BitVec 8) :
    x + (x &&& 42#8) * 255#8 = x &&& 213#8 := by
  bv_decide

