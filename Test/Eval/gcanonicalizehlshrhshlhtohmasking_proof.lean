import LeanSAT.Tactics.BVDecide



theorem canonicalize_shrshlhtomasking_positive_sameconst_thm (x : _root_.BitVec 8) :
    x >>> 3 <<< 3 = x &&& 248#8 := by
  bv_decide

theorem canonicalize_shrshlhtomasking_positive_biggerlshr_thm (x : _root_.BitVec 8) :
    x >>> 6 <<< 3 = x >>> 3 &&& 24#8 := by
  bv_decide

theorem canonicalize_shrshlhtomasking_positive_biggershl_thm (x : _root_.BitVec 8) :
    x >>> 3 <<< 6 = x <<< 3 &&& 192#8 := by
  bv_decide

theorem canonicalize_shrshlhtomasking_positive_sameconst_shlnuw_thm (x : _root_.BitVec 8) :
    x >>> 3 <<< 3 = x &&& 248#8 := by
  bv_decide

theorem canonicalize_shrshlhtomasking_positive_biggerlshr_shlnuw_thm (x : _root_.BitVec 8) :
    x >>> 6 <<< 3 = x >>> 3 &&& 24#8 := by
  bv_decide

theorem canonicalize_shrshlhtomasking_positive_biggershl_shlnuw_thm (x : _root_.BitVec 8) :
    x >>> 3 <<< 6 = x <<< 3 &&& 192#8 := by
  bv_decide

theorem canonicalize_shrshlhtomasking_positive_sameconst_shlnsw_thm (x : _root_.BitVec 8) :
    x >>> 3 <<< 3 = x &&& 248#8 := by
  bv_decide

theorem canonicalize_shrshlhtomasking_positive_biggerlshr_shlnsw_thm (x : _root_.BitVec 8) :
    x >>> 6 <<< 3 = x >>> 3 &&& 24#8 := by
  bv_decide

theorem canonicalize_shrshlhtomasking_positive_sameconst_shlnuwnsw_thm (x : _root_.BitVec 8) :
    x >>> 3 <<< 3 = x &&& 248#8 := by
  bv_decide

theorem canonicalize_shrshlhtomasking_positive_biggerlshr_shlnuwnsw_thm (x : _root_.BitVec 8) :
    x >>> 6 <<< 3 = x >>> 3 &&& 24#8 := by
  bv_decide
