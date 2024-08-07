import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem match_andAsRem_lshrAsDiv_shlAsMul_thm (x : _root_.BitVec 64) :
  (x &&& 63#64) + BitVec.ofNat 64 (x.toNat >>> 6 % 9) <<< 6 = BitVec.ofNat 64 (x.toNat % 576) := by
  bv_decide

theorem match_signed_thm (x : _root_.BitVec 64) :
  x + 299#64 * (x.sdiv 299#64).sdiv 64#64 * 18446744073709551552#64 + x.sdiv 19136#64 * 19136#64 +
      (x.sdiv 19136#64).sdiv 9#64 * 18446744073709379392#64 =
    x + x.sdiv 172224#64 * 18446744073709379392#64 := by
  bv_decide

theorem not_match_inconsistent_signs_thm (x : _root_.BitVec 64) :
  BitVec.ofNat 64 ((x.sdiv 299#64).toNat % 64) * 299#64 = 299#64 * (x.sdiv 299#64 &&& 63#64) := by
  bv_decide

