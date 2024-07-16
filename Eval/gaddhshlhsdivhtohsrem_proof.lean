import LeanSAT.Tactics.BVDecide

open Std (BitVec)

theorem addhshlhsdivhscalar0_thm (x : _root_.BitVec 8) :
    x.sdiv 252#8 <<< 2 + x = x + x.sdiv 4#8 * 252#8 := by
  bv_decide

theorem addhshlhsdivhscalar1_thm (x : _root_.BitVec 8) :
    x.sdiv 192#8 <<< 6 + x = x + x.sdiv 64#8 * 192#8 := by
  bv_decide

theorem addhshlhsdivhscalar2_thm (x : _root_.BitVec 32) :
  x.sdiv 3221225472#32 <<< 30 + x = x + x.sdiv 1073741824#32 * 3221225472#32 := by
  bv_decide
