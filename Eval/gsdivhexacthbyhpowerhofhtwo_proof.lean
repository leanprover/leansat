import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem t0_thm (x : _root_.BitVec 8) :
    x.sdiv 32#8 = x.sshiftRight 5 := by
  bv_decide


theorem prove_exact_with_high_mask_thm (x : _root_.BitVec 8) :
    (x &&& 248#8).sdiv 4#8 = x.sshiftRight 2 &&& 254#8 := by
  bv_decide

theorem prove_exact_with_high_mask_limit_thm (x : _root_.BitVec 8) :
    (x &&& 248#8).sdiv 8#8 = x.sshiftRight 3 := by
  bv_decide

