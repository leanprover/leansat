import LeanSAT.Tactics.BVDecide



theorem positive_sameconst_thm (x : _root_.BitVec 8) :
    x.sshiftRight 3 <<< 3 = x &&& 248#8 := by
  bv_decide

theorem positive_biggerashr_thm (x : _root_.BitVec 8) :
    x.sshiftRight 6 <<< 3 = x.sshiftRight 3 &&& 248#8 := by
  bv_decide

theorem positive_biggershl_thm (x : _root_.BitVec 8) :
    x.sshiftRight 3 <<< 6 = x <<< 3 &&& 192#8 := by
  bv_decide

theorem positive_sameconst_shlnuw_thm (x : _root_.BitVec 8) :
    x.sshiftRight 3 <<< 3 = x &&& 248#8 := by
  bv_decide

theorem positive_biggerashr_shlnuw_thm (x : _root_.BitVec 8) :
    x.sshiftRight 6 <<< 3 = x.sshiftRight 3 &&& 248#8 := by
  bv_decide

theorem positive_biggershl_shlnuw_thm (x : _root_.BitVec 8) :
    x.sshiftRight 3 <<< 6 = x <<< 3 &&& 192#8 := by
  bv_decide

theorem positive_sameconst_shlnsw_thm (x : _root_.BitVec 8) :
    x.sshiftRight 3 <<< 3 = x &&& 248#8 := by
  bv_decide

theorem positive_biggerashr_shlnsw_thm (x : _root_.BitVec 8) :
    x.sshiftRight 6 <<< 3 = x.sshiftRight 3 &&& 248#8 := by
  bv_decide

theorem positive_biggershl_shlnsw_thm (x : _root_.BitVec 8) :
    x.sshiftRight 3 <<< 6 = x <<< 3 &&& 192#8 := by
  bv_decide

theorem positive_sameconst_shlnuwnsw_thm (x : _root_.BitVec 8) :
    x.sshiftRight 3 <<< 3 = x &&& 248#8 := by
  bv_decide

theorem positive_biggerashr_shlnuwnsw_thm (x : _root_.BitVec 8) :
    x.sshiftRight 6 <<< 3 = x.sshiftRight 3 &&& 248#8 := by
  bv_decide
