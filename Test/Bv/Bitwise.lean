import LeanSAT.Reflect.Tactics.BVDecide

open BitVec

set_option trace.bv true in
theorem bitwise_unit_1 {x y : BitVec 64} : ~~~(x &&& y) = (~~~x ||| ~~~y) := by
  bv_decide

set_option trace.bv true in
theorem bitwise_unit_1' {x y : BitVec 64} : ~~~(BitVec.and x y) = ((BitVec.not x) ||| ~~~y) := by
  bv_decide

set_option trace.bv true in
theorem bitwise_unit_2 {x : BitVec 64} : x ^^^ x = 0 := by
  bv_decide

set_option trace.bv true in
theorem bitwise_unit_2' {x : BitVec 64} : (BitVec.xor x x) = 0 := by
  bv_decide

set_option trace.bv true in
theorem bitwise_unit_3 {x : BitVec 64} : (x ^^^ x).getLsb 32 = false := by
  bv_decide

set_option trace.bv true in
theorem bitwise_unit_4 {x : BitVec 64} : (x ^^^ ~~~x).getLsb 32 = true := by
  bv_decide

set_option trace.bv true in
theorem bitwise_unit_5 {x : BitVec 64} : (x ^^^ ~~~x).getLsb 128 = false := by
  bv_decide
