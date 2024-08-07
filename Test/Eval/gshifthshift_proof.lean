import LeanSAT.Tactics.BVDecide


theorem shl_shl_thm (x : _root_.BitVec 32) :
    x <<< 34 = 0#32 := by
  bv_decide
