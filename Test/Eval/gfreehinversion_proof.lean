import LeanSAT.Tactics.BVDecide


theorem lshr_not_nneg2_thm (x : _root_.BitVec 8) :
    (x ^^^ 255#8) >>> 1 ^^^ 255#8 = x >>> 1 ||| 128#8 := by
  bv_decide

