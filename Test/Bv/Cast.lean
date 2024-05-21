import LeanSAT.Reflect.Tactics.BVDecide

open BitVec

set_option trace.bv true in
theorem cast_unit_1 (x : BitVec 64) : Nat.cast 0 &&& x = 0 := by
  bv_decide

set_option trace.bv true in
theorem cast_unit_2 (x : BitVec 64) : x.zeroExtend 32 = (x.zeroExtend 64).zeroExtend 32 := by
  bv_decide

set_option trace.bv true in
theorem cast_unit_3 (x : BitVec 64) : x.zeroExtend 128 = (x.zeroExtend 64).zeroExtend 128 := by
  bv_decide

set_option trace.bv true in
theorem cast_unit_3' (x : BitVec 64) : x.truncate 128 = (x.truncate 64).zeroExtend 128 := by
  bv_decide

set_option trace.bv true in
theorem cast_unit_4 (x y : BitVec 32) : (x.zeroExtend 64).extractLsb 32 0 = (y.zeroExtend 64).extractLsb 32 0 → x = y := by
  bv_decide

set_option trace.bv true in
theorem cast_unit_5 (x y : BitVec 64) : (x ++ y).extractLsb 63 0 = (y ++ x).extractLsb 127 64 := by
  bv_decide

set_option trace.bv true in
theorem cast_unit_5' (x y : BitVec 64) : (BitVec.append x y).extractLsb 63 0 = (y ++ x).extractLsb 127 64 := by
  bv_decide
