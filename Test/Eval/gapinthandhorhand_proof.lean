import LeanSAT.Tactics.BVDecide


theorem horand_test1_thm (x x_1 : _root_.BitVec 17) :
    (x_1 &&& 7#17 ||| x &&& 8#17) &&& 7#17 = x_1 &&& 7#17 := by
  bv_decide

theorem horand_test3_thm (x x_1 : _root_.BitVec 49) :
    (x_1 ||| x <<< 1) &&& 1#49 = x_1 &&& 1#49 := by
  bv_decide

theorem horand_test4_thm (x x_1 : _root_.BitVec 67) :
    (x_1 ||| x >>> 66) &&& 2#67 = x_1 &&& 2#67 := by
  bv_decide

theorem horand_or_test2_thm (x : _root_.BitVec 7) :
    x <<< 6 ||| 64#7 = 64#7 := by
  bv_decide

