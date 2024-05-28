import LeanSAT.Reflect.Tactics.BVDecide

open BitVec

set_option trace.bv true in
theorem shift_unit_1 {x y : BitVec 64} : x <<< 65 = y <<< 66 := by
  bv_decide

set_option trace.bv true in
theorem shift_unit_1' {x y : BitVec 64} : BitVec.shiftLeft x 65 = y >>> 66 := by
  bv_decide

set_option trace.bv true in
theorem shift_unit_2 {x y : BitVec 64} : x >>> 65 = y >>> 66 := by
  bv_decide

set_option trace.bv true in
theorem shift_unit_2' {x y : BitVec 64} : BitVec.ushiftRight x 65 = y >>> 66 := by
  bv_decide

set_option trace.bv true in
theorem shift_unit_3 {x : BitVec 64} : (x <<< 32) <<< 32 = (x >>> 32) >>> 32 := by
  bv_decide

-- This demonstrates we correctly abstract shifts of arbitrary width as atoms instead of giving up.
set_option trace.bv true in
theorem shift_unit_5 {x y : BitVec 64} : (x <<< y) + y = y + (x <<< y) := by
  bv_decide

-- This demonstrates we correctly abstract shifts of arbitrary width as atoms instead of giving up.
set_option trace.bv true in
theorem shift_unit_6 {x y : BitVec 64} : (x >>> y) + y = y + (x >>> y) := by
  bv_decide

set_option trace.bv true in
theorem rotate_unit_1 {x : BitVec 64} : BitVec.rotateLeft x 0 = x := by
  bv_decide

set_option trace.bv true in
theorem rotate_unit_2 {x : BitVec 64} : BitVec.rotateLeft x 64 = x := by
  bv_decide

set_option trace.bv true in
theorem rotate_unit_3 {x : BitVec 64} : BitVec.rotateLeft x 16 = (BitVec.rotateLeft (BitVec.rotateLeft x 6) 10) := by
  bv_decide

set_option trace.bv true in
theorem rotate_unit_4 {x : BitVec 64} : BitVec.rotateLeft x (64 + 16) = (BitVec.rotateLeft x 16) := by
  bv_decide
