import LeanSAT.Tactics.BVDecide


theorem basic_thm (x x_1 : _root_.BitVec 8) :
    (x_1 ^^^ 255#8) + x ^^^ 255#8 = x * 255#8 + x_1 := by
  bv_decide

theorem basic_com_add_thm (x x_1 : _root_.BitVec 8) :
    x_1 + (x ^^^ 255#8) ^^^ 255#8 = x_1 * 255#8 + x := by
  bv_decide

theorem basic_preserve_nsw_thm (x x_1 : _root_.BitVec 8) :
    (x_1 ^^^ 255#8) + x ^^^ 255#8 = x * 255#8 + x_1 := by
  bv_decide

theorem basic_preserve_nuw_thm (x x_1 : _root_.BitVec 8) :
    (x_1 ^^^ 255#8) + x ^^^ 255#8 = x * 255#8 + x_1 := by
  bv_decide

theorem basic_preserve_nuw_nsw_thm (x x_1 : _root_.BitVec 8) :
    (x_1 ^^^ 255#8) + x ^^^ 255#8 = x * 255#8 + x_1 := by
  bv_decide

