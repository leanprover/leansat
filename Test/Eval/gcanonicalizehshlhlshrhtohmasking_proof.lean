import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem gcanonicalize_shrshlhtomasking_positive_sameconst_thm (x : _root_.BitVec 32) :
    x <<< 5 >>> 5 = x &&& 134217727#32 := by
  bv_decide

theorem gcanonicalize_shrshlhtomasking_positive_biggerShl_thm (x : _root_.BitVec 32) :
    x <<< 10 >>> 5 = x <<< 5 &&& 134217696#32 := by
  bv_decide

theorem gcanonicalize_shrshlhtomasking_positive_biggerLshr_thm (x : _root_.BitVec 32) :
    x <<< 5 >>> 10 = x >>> 5 &&& 4194303#32 := by
  bv_decide

theorem gcanonicalize_shrshlhtomasking_positive_biggerLshr_lshrexact_thm (x : _root_.BitVec 32) :
    x <<< 5 >>> 10 = x >>> 5 &&& 4194303#32 := by
  bv_decide
