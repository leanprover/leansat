import LeanSAT.Tactics.BVDecide


theorem calculation_t0_thm (x x_1 : _root_.BitVec 8) :
    255#8 * x + (x_1 * 255#8 &&& x) = 255#8 * (x_1 + 255#8 &&& x) := by
  bv_decide

theorem calculation_n7_thm (x x_1 : _root_.BitVec 8) :
    x_1 + 255#8 * (x * 255#8 &&& x_1) = x + 255#8 &&& x_1 := by
  bv_decide

