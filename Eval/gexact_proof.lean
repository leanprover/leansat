import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem sdiv2_thm (x : _root_.BitVec 32) :
    x.sdiv 8#32 = x.sshiftRight 3 := by
  bv_decide

theorem sdiv4_thm (x : _root_.BitVec 32) :
    x.sdiv 3#32 * 3#32 = x := by
  bv_decide

theorem sdiv6_thm (x : _root_.BitVec 32) :
    x.sdiv 3#32 * 4294967293#32 = x * 4294967295#32 := by
  bv_decide

theorem mul_of_sdiv_fail_ub_thm (x : _root_.BitVec 8) :
    x.sdiv 6#8 * 250#8 = x * 255#8 := by
  bv_decide

