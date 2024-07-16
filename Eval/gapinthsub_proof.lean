import LeanSAT.Tactics.BVDecide

set_option sat.timeout 1
open Std (BitVec)
theorem test6_thm (x x_1 : _root_.BitVec 57) :
  x_1 + (x_1 &&& x) * 144115188075855871#57 = (x ^^^ 144115188075855871#57) &&& x_1 := by
  bv_decide

theorem test7_thm (x : _root_.BitVec 77) :
  151115727451828646838271#77 + 151115727451828646838271#77 * x = x ^^^ 151115727451828646838271#77 := by
  bv_decide
#exit
theorem test8_thm (x : _root_.BitVec 27) :
    9#27 * x + x * 134217727#27 = x <<< 3 := by
  bv_decide

theorem test9_thm (x : _root_.BitVec 42) :
    x + x * 4398046511101#42 = x * 4398046511102#42 := by
  bv_decide

theorem test12_thm (x : _root_.BitVec 43) :
    x.sshiftRight 42 * 8796093022207#43 = x >>> 42 := by
  bv_decide

theorem test13_thm (x : _root_.BitVec 79) :
    x >>> 78 * 604462909807314587353087#79 = x.sshiftRight 78 := by
  bv_decide

theorem test16_thm (x : _root_.BitVec 51) :
    x.sdiv 1123#51 * 2251799813685247#51 = x.sdiv 2251799813684125#51 := by
  bv_decide

