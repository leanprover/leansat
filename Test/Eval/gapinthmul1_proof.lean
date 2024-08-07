import LeanSAT.Tactics.BVDecide



theorem inthmul1_test1_thm (x : _root_.BitVec 17) :
    x * 1024#17 = x <<< 10 := by
  bv_decide

