import LeanSAT.Tactics.BVDecide


theorem gunfoldhmaskedhmergewithhconsthmaskhscalar_scalar0_thm (x x_1 : _root_.BitVec 4) :
    (x_1 ^^^ x) &&& 1#4 ^^^ x = x_1 &&& 1#4 ||| x &&& 14#4 := by
  bv_decide

theorem gunfoldhmaskedhmergewithhconsthmaskhscalar_scalar1_thm (x x_1 : _root_.BitVec 4) :
    (x_1 ^^^ x) &&& 14#4 ^^^ x = x_1 &&& 14#4 ||| x &&& 1#4 := by
  bv_decide

theorem gunfoldhmaskedhmergewithhconsthmaskhscalar_in_constant_varx_mone_thm (x : _root_.BitVec 4) :
    (x ^^^ 15#4) &&& 1#4 ^^^ 15#4 = x ||| 14#4 := by
  bv_decide

theorem gunfoldhmaskedhmergewithhconsthmaskhscalar_in_constant_varx_14_thm (x : _root_.BitVec 4) :
    (x ^^^ 14#4) &&& 1#4 ^^^ 14#4 = x ||| 14#4 := by
  bv_decide

theorem gunfoldhmaskedhmergewithhconsthmaskhscalar_in_constant_mone_vary_thm (x : _root_.BitVec 4) :
    (x ^^^ 15#4) &&& 1#4 ^^^ x = x ||| 1#4 := by
  bv_decide

theorem gunfoldhmaskedhmergewithhconsthmaskhscalar_in_constant_14_vary_thm (x : _root_.BitVec 4) :
    (x ^^^ 14#4) &&& 1#4 ^^^ x = x &&& 14#4 := by
  bv_decide

theorem gunfoldhmaskedhmergewithhconsthmaskhscalar_c_1_0_0_thm (x x_1 : _root_.BitVec 4) :
    (x_1 ^^^ x) &&& 14#4 ^^^ x_1 = x &&& 14#4 ||| x_1 &&& 1#4 := by
  bv_decide

theorem gunfoldhmaskedhmergewithhconsthmaskhscalar_c_0_1_0_thm (x x_1 : _root_.BitVec 4) :
    (x_1 ^^^ x) &&& 14#4 ^^^ x_1 = x &&& 14#4 ||| x_1 &&& 1#4 := by
  bv_decide

theorem gunfoldhmaskedhmergewithhconsthmaskhscalar_c_1_1_0_thm (x x_1 : _root_.BitVec 4) :
    (x_1 ^^^ x) &&& 14#4 ^^^ x = x_1 &&& 14#4 ||| x &&& 1#4 := by
  bv_decide

theorem gunfoldhmaskedhmergewithhconsthmaskhscalar_commutativity_constant_14_vary_thm (x : _root_.BitVec 4) :
    x ^^^ (x ^^^ 14#4) &&& 1#4 = x &&& 14#4 := by
  bv_decide

