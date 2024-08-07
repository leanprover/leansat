import LeanSAT.Tactics.BVDecide


theorem sub_not_thm (x x_1 : _root_.BitVec 8) :
    x_1 + x * 255#8 ^^^ 255#8 = x + (x_1 ^^^ 255#8) := by
  bv_decide

theorem dec_sub_thm (x x_1 : _root_.BitVec 8) :
    x_1 + x * 255#8 + 255#8 = x_1 + (x ^^^ 255#8) := by
  bv_decide

theorem sub_inc_thm (x x_1 : _root_.BitVec 8) :
    x_1 + x * 255#8 + 255#8 = x_1 + (x ^^^ 255#8) := by
  bv_decide

theorem sub_dec_thm (x x_1 : _root_.BitVec 8) :
    x_1 + 255#8 + 255#8 * x = x_1 + (x ^^^ 255#8) := by
  bv_decide

