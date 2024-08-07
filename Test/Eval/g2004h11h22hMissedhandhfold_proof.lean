import LeanSAT.Tactics.BVDecide


theorem test21_thm (x : _root_.BitVec 8) :
    x.sshiftRight 7 &&& 1#8 = x >>> 7 := by
  bv_decide

