import LeanSAT.Tactics.BVDecide


theorem t0_thm (x : _root_.BitVec 64) :
    x >>> 63 * 18446744073709551615#64 = x.sshiftRight 63 := by
  bv_decide

theorem t0_exact_thm (x : _root_.BitVec 64) :
    x >>> 63 * 18446744073709551615#64 = x.sshiftRight 63 := by
  bv_decide

theorem t2_thm (x : _root_.BitVec 64) :
    x.sshiftRight 63 * 18446744073709551615#64 = x >>> 63 := by
  bv_decide

theorem t3_exact_thm (x : _root_.BitVec 64) :
    x.sshiftRight 63 * 18446744073709551615#64 = x >>> 63 := by
  bv_decide

