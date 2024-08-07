import LeanSAT.Tactics.BVDecide


theorem inthmul2_test1_thm (x : _root_.BitVec 177) :
  x * 45671926166590716193865151022383844364247891968#177 = x <<< 155 := by
  bv_decide

