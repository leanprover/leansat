import LeanSAT.Tactics.BVDecide


theorem and_xor_not_common_op_thm (x x_1 : _root_.BitVec 32) :
    (x_1 ^^^ (x ^^^ 4294967295#32)) &&& x_1 = x_1 &&& x := by
  bv_decide

theorem and_not_xor_common_op_thm (x x_1 : _root_.BitVec 32) :
    (x_1 ^^^ x ^^^ 4294967295#32) &&& x = x &&& x_1 := by
  bv_decide

theorem not_and_and_not_commute1_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32) &&& x_1 &&& (x ^^^ 4294967295#32) = ((x_2 ||| x) ^^^ 4294967295#32) &&& x_1 := by
  bv_decide

theorem not_or_or_not_commute1_thm (x x_1 x_2 : _root_.BitVec 32) :
  x_2 ^^^ 4294967295#32 ||| x_1 ||| x ^^^ 4294967295#32 = x_2 &&& x ^^^ 4294967295#32 ||| x_1 := by
  bv_decide

theorem or_not_and_thm (x x_1 x_2 : _root_.BitVec 32) :
  ((x_2 ||| x_1) ^^^ 4294967295#32) &&& x ||| ((x_2 ||| x) ^^^ 4294967295#32) &&& x_1 =
    (x_1 ^^^ x) &&& (x_2 ^^^ 4294967295#32) := by
  bv_decide

theorem or_not_and_commute3_thm (x x_1 x_2 : _root_.BitVec 32) :
  ((x_2 ||| x_1) ^^^ 4294967295#32) &&& x ||| ((x ||| x_1) ^^^ 4294967295#32) &&& x_2 =
    (x_2 ^^^ x) &&& (x_1 ^^^ 4294967295#32) := by
  bv_decide

theorem or_not_and_commute6_thm (x x_1 x_2 : _root_.BitVec 32) :
  ((x_2 ||| x_1) ^^^ 4294967295#32) &&& x ||| ((x ||| x_2) ^^^ 4294967295#32) &&& x_1 =
    (x_1 ^^^ x) &&& (x_2 ^^^ 4294967295#32) := by
  bv_decide

theorem or_not_and_commute7_thm (x x_1 x_2 : _root_.BitVec 32) :
  ((x_2 ||| x_1) ^^^ 4294967295#32) &&& x ||| ((x_1 ||| x) ^^^ 4294967295#32) &&& x_2 =
    (x_2 ^^^ x) &&& (x_1 ^^^ 4294967295#32) := by
  bv_decide

theorem and_not_or_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) &&& (x_2 &&& x ^^^ 4294967295#32 ||| x_1) =
    (x_1 ^^^ x) &&& x_2 ^^^ 4294967295#32 := by
  bv_decide

theorem and_not_or_commute3_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) &&& (x &&& x_1 ^^^ 4294967295#32 ||| x_2) =
    (x_2 ^^^ x) &&& x_1 ^^^ 4294967295#32 := by
  bv_decide

theorem and_not_or_commute6_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) &&& (x &&& x_2 ^^^ 4294967295#32 ||| x_1) =
    (x_1 ^^^ x) &&& x_2 ^^^ 4294967295#32 := by
  bv_decide

theorem and_not_or_commute7_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) &&& (x_1 &&& x ^^^ 4294967295#32 ||| x_2) =
    (x_2 ^^^ x) &&& x_1 ^^^ 4294967295#32 := by
  bv_decide

theorem or_and_not_not_thm (x x_1 x_2 : _root_.BitVec 32) :
  ((x_2 ||| x_1) ^^^ 4294967295#32) &&& x ||| (x ||| x_2) ^^^ 4294967295#32 =
    (x_1 &&& x ||| x_2) ^^^ 4294967295#32 := by
  bv_decide

theorem or_and_not_not_commute2_thm (x x_1 x_2 : _root_.BitVec 32) :
  ((x_2 ||| x_1) ^^^ 4294967295#32) &&& x ||| (x ||| x_2) ^^^ 4294967295#32 =
    (x_1 &&& x ||| x_2) ^^^ 4294967295#32 := by
  bv_decide

theorem or_and_not_not_commute3_thm (x x_1 x_2 : _root_.BitVec 32) :
  ((x_2 ||| x_1) ^^^ 4294967295#32) &&& x ||| (x ||| x_1) ^^^ 4294967295#32 =
    (x_2 &&& x ||| x_1) ^^^ 4294967295#32 := by
  bv_decide

theorem or_and_not_not_commute4_thm (x x_1 x_2 : _root_.BitVec 32) :
  ((x_2 ||| x_1) ^^^ 4294967295#32) &&& x ||| (x_2 ||| x) ^^^ 4294967295#32 =
    (x_1 &&& x ||| x_2) ^^^ 4294967295#32 := by
  bv_decide

theorem or_and_not_not_commute5_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ||| x_1) ^^^ 4294967295#32 ||| ((x_1 ||| x) ^^^ 4294967295#32) &&& x_2 =
    (x &&& x_2 ||| x_1) ^^^ 4294967295#32 := by
  bv_decide

theorem and_or_not_not_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) &&& (x &&& x_2 ^^^ 4294967295#32) =
    (x_1 ||| x) &&& x_2 ^^^ 4294967295#32 := by
  bv_decide

theorem and_or_not_not_commute2_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) &&& (x &&& x_2 ^^^ 4294967295#32) =
    (x_1 ||| x) &&& x_2 ^^^ 4294967295#32 := by
  bv_decide

theorem and_or_not_not_commute3_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) &&& (x &&& x_1 ^^^ 4294967295#32) =
    (x_2 ||| x) &&& x_1 ^^^ 4294967295#32 := by
  bv_decide

theorem and_or_not_not_commute4_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) &&& (x_2 &&& x ^^^ 4294967295#32) =
    (x_1 ||| x) &&& x_2 ^^^ 4294967295#32 := by
  bv_decide

theorem and_or_not_not_commute5_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 &&& x_1 ^^^ 4294967295#32) &&& (x_1 &&& x ^^^ 4294967295#32 ||| x_2) =
    (x ||| x_2) &&& x_1 ^^^ 4294967295#32 := by
  bv_decide

theorem and_or_not_not_wrong_a_thm (x x_1 x_2 x_3 : _root_.BitVec 32) :
  (x_3 &&& x_2 ^^^ 4294967295#32 ||| x_1) &&& (x_1 &&& x ^^^ 4294967295#32) =
    x_1 &&& x ^^^ (x_3 &&& x_2 ^^^ 4294967295#32 ||| x_1) := by
  bv_decide

theorem and_not_or_or_not_or_xor_thm (x x_1 x_2 : _root_.BitVec 32) :
  ((x_2 ||| x_1) ^^^ 4294967295#32) &&& x ||| (x_2 ^^^ x_1 ||| x) ^^^ 4294967295#32 =
    (x_2 ||| x_1) &&& (x_2 ^^^ x_1 ||| x) ^^^ 4294967295#32 := by
  bv_decide

theorem and_not_or_or_not_or_xor_commute1_thm (x x_1 x_2 : _root_.BitVec 32) :
  ((x_2 ||| x_1) ^^^ 4294967295#32) &&& x ||| (x_1 ^^^ x_2 ||| x) ^^^ 4294967295#32 =
    (x_2 ||| x_1) &&& (x_1 ^^^ x_2 ||| x) ^^^ 4294967295#32 := by
  bv_decide

theorem and_not_or_or_not_or_xor_commute3_thm (x x_1 x_2 : _root_.BitVec 32) :
  ((x_2 ||| x_1) ^^^ 4294967295#32) &&& x ||| (x_1 ^^^ x_2 ||| x) ^^^ 4294967295#32 =
    (x_2 ||| x_1) &&& (x_1 ^^^ x_2 ||| x) ^^^ 4294967295#32 := by
  bv_decide

theorem and_not_or_or_not_or_xor_commute5_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ x_1 ||| x) ^^^ 4294967295#32 ||| ((x_2 ||| x_1) ^^^ 4294967295#32) &&& x =
    (x_2 ||| x_1) &&& (x_2 ^^^ x_1 ||| x) ^^^ 4294967295#32 := by
  bv_decide

theorem or_not_and_and_not_and_xor_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) &&& ((x_2 ^^^ x_1) &&& x ^^^ 4294967295#32) =
    (x_2 ^^^ x_1) &&& x ^^^ (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) := by
  bv_decide

theorem or_not_and_and_not_and_xor_commute1_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) &&& ((x_1 ^^^ x_2) &&& x ^^^ 4294967295#32) =
    (x_1 ^^^ x_2) &&& x ^^^ (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) := by
  bv_decide

theorem or_not_and_and_not_and_xor_commute3_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) &&& ((x_1 ^^^ x_2) &&& x ^^^ 4294967295#32) =
    (x_1 ^^^ x_2) &&& x ^^^ (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) := by
  bv_decide

theorem or_not_and_and_not_and_xor_commute5_thm (x x_1 x_2 : _root_.BitVec 32) :
  ((x_2 ^^^ x_1) &&& x ^^^ 4294967295#32) &&& (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) =
    (x_2 ^^^ x_1) &&& x ^^^ (x_2 &&& x_1 ^^^ 4294967295#32 ||| x) := by
  bv_decide

theorem not_and_and_or_not_or_or_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32) &&& x_1 &&& x ||| (x_1 ||| x_2 ||| x) ^^^ 4294967295#32 =
    (x ^^^ x_1 ||| x_2) ^^^ 4294967295#32 := by
  bv_decide

theorem not_and_and_or_not_or_or_commute2_or_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32) &&& x_1 &&& x ||| (x_1 ||| x ||| x_2) ^^^ 4294967295#32 =
    (x ^^^ x_1 ||| x_2) ^^^ 4294967295#32 := by
  bv_decide

theorem not_and_and_or_not_or_or_commute1_and_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32) &&& x_1 &&& x ||| (x ||| x_2 ||| x_1) ^^^ 4294967295#32 =
    (x ^^^ x_1 ||| x_2) ^^^ 4294967295#32 := by
  bv_decide

theorem not_and_and_or_not_or_or_commute2_and_thm (x x_1 x_2 : _root_.BitVec 32) :
  x_2 &&& x_1 &&& (x ^^^ 4294967295#32) ||| (x_2 ||| x ||| x_1) ^^^ 4294967295#32 =
    (x_2 ^^^ x_1 ||| x) ^^^ 4294967295#32 := by
  bv_decide

theorem not_and_and_or_not_or_or_commute1_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32) &&& x_1 &&& x ||| (x_2 ||| x_1 ||| x) ^^^ 4294967295#32 =
    (x ^^^ x_1 ||| x_2) ^^^ 4294967295#32 := by
  bv_decide

theorem not_or_or_and_not_and_and_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32 ||| x_1 ||| x) &&& (x_1 &&& x_2 &&& x ^^^ 4294967295#32) =
    x ^^^ x_1 ||| x_2 ^^^ 4294967295#32 := by
  bv_decide

theorem not_or_or_and_not_and_and_commute1_and_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32 ||| x_1 ||| x) &&& (x &&& x_2 &&& x_1 ^^^ 4294967295#32) =
    x ^^^ x_1 ||| x_2 ^^^ 4294967295#32 := by
  bv_decide

theorem not_or_or_and_not_and_and_commute2_and_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32 ||| x_1 ||| x) &&& (x_1 &&& x &&& x_2 ^^^ 4294967295#32) =
    x ^^^ x_1 ||| x_2 ^^^ 4294967295#32 := by
  bv_decide

theorem not_or_or_and_not_and_and_commute1_or_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32 ||| x_1 ||| x) &&& (x &&& x_2 &&& x_1 ^^^ 4294967295#32) =
    x ^^^ x_1 ||| x_2 ^^^ 4294967295#32 := by
  bv_decide

theorem not_or_or_and_not_and_and_commute2_or_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ||| x_1 ||| x ^^^ 4294967295#32) &&& (x_2 &&& x &&& x_1 ^^^ 4294967295#32) =
    x_2 ^^^ x_1 ||| x ^^^ 4294967295#32 := by
  bv_decide

theorem not_or_or_and_not_and_and_commute1_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32 ||| x_1 ||| x) &&& (x_2 &&& x_1 &&& x ^^^ 4294967295#32) =
    x ^^^ x_1 ||| x_2 ^^^ 4294967295#32 := by
  bv_decide

theorem not_and_and_or_no_or_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32) &&& x_1 &&& x ||| (x_1 ||| x_2) ^^^ 4294967295#32 =
    (x_1 ^^^ 4294967295#32 ||| x) &&& (x_2 ^^^ 4294967295#32) := by
  bv_decide

theorem not_and_and_or_no_or_commute1_and_thm (x x_1 x_2 : _root_.BitVec 32) :
  x_2 &&& x_1 &&& (x ^^^ 4294967295#32) ||| (x_1 ||| x) ^^^ 4294967295#32 =
    (x_1 ^^^ 4294967295#32 ||| x_2) &&& (x ^^^ 4294967295#32) := by
  bv_decide

theorem not_and_and_or_no_or_commute2_and_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32) &&& x_1 &&& x ||| (x ||| x_2) ^^^ 4294967295#32 =
    (x ^^^ 4294967295#32 ||| x_1) &&& (x_2 ^^^ 4294967295#32) := by
  bv_decide

theorem not_and_and_or_no_or_commute1_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32) &&& x_1 &&& x ||| (x_2 ||| x_1) ^^^ 4294967295#32 =
    (x_1 ^^^ 4294967295#32 ||| x) &&& (x_2 ^^^ 4294967295#32) := by
  bv_decide

theorem not_or_or_and_no_and_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32 ||| x_1 ||| x) &&& (x_1 &&& x_2 ^^^ 4294967295#32) =
    (x_1 ^^^ 4294967295#32) &&& x ||| x_2 ^^^ 4294967295#32 := by
  bv_decide

theorem not_or_or_and_no_and_commute1_or_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ||| x_1 ||| x ^^^ 4294967295#32) &&& (x_1 &&& x ^^^ 4294967295#32) =
    (x_1 ^^^ 4294967295#32) &&& x_2 ||| x ^^^ 4294967295#32 := by
  bv_decide

theorem not_or_or_and_no_and_commute2_or_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32 ||| x_1 ||| x) &&& (x &&& x_2 ^^^ 4294967295#32) =
    (x ^^^ 4294967295#32) &&& x_1 ||| x_2 ^^^ 4294967295#32 := by
  bv_decide

theorem not_or_or_and_no_and_commute1_thm (x x_1 x_2 : _root_.BitVec 32) :
  (x_2 ^^^ 4294967295#32 ||| x_1 ||| x) &&& (x_2 &&& x_1 ^^^ 4294967295#32) =
    (x_1 ^^^ 4294967295#32) &&& x ||| x_2 ^^^ 4294967295#32 := by
  bv_decide

theorem and_orn_xor_thm (x x_1 : _root_.BitVec 4) :
    (x_1 ^^^ 15#4 ||| x) &&& (x_1 ^^^ x) = (x_1 ^^^ 15#4) &&& x := by
  bv_decide

theorem canonicalize_logic_first_or0_thm (x : _root_.BitVec 32) :
    x + 112#32 ||| 15#32 = 112#32 + (x ||| 15#32) := by
  bv_decide

theorem canonicalize_logic_first_or0_nsw_thm (x : _root_.BitVec 32) :
    x + 112#32 ||| 15#32 = 112#32 + (x ||| 15#32) := by
  bv_decide

theorem canonicalize_logic_first_or0_nswnuw_thm (x : _root_.BitVec 32) :
    x + 112#32 ||| 15#32 = 112#32 + (x ||| 15#32) := by
  bv_decide

theorem canonicalize_logic_first_and0_thm (x : _root_.BitVec 8) :
    x + 48#8 &&& 246#8 = 48#8 + (x &&& 246#8) := by
  bv_decide

theorem canonicalize_logic_first_and0_nsw_thm (x : _root_.BitVec 8) :
    x + 48#8 &&& 246#8 = 48#8 + (x &&& 246#8) := by
  bv_decide

theorem canonicalize_logic_first_and0_nswnuw_thm (x : _root_.BitVec 8) :
    x + 48#8 &&& 246#8 = 48#8 + (x &&& 246#8) := by
  bv_decide

theorem canonicalize_logic_first_xor_0_thm (x : _root_.BitVec 8) :
    x + 96#8 ^^^ 31#8 = 96#8 + (x ^^^ 31#8) := by
  bv_decide

theorem canonicalize_logic_first_xor_0_nsw_thm (x : _root_.BitVec 8) :
    x + 96#8 ^^^ 31#8 = 96#8 + (x ^^^ 31#8) := by
  bv_decide

theorem canonicalize_logic_first_xor_0_nswnuw_thm (x : _root_.BitVec 8) :
    x + 96#8 ^^^ 31#8 = 96#8 + (x ^^^ 31#8) := by
  bv_decide

