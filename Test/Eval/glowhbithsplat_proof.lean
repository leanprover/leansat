import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem bithsplat_t0_thm (x : _root_.BitVec 8) :
    (x <<< 7).sshiftRight 7 = (x &&& 1#8) * 255#8 := by
  bv_decide

theorem bithsplat_t1_otherbitwidth_thm (x : _root_.BitVec 16) :
    (x <<< 15).sshiftRight 15 = (x &&& 1#16) * 65535#16 := by
  bv_decide

