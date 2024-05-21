import LeanSAT.Reflect.Tactics.BVDecide

open BitVec

set_option trace.bv true in
theorem substructure_unit_1 (x y z : BitVec 8) : ((x = y) ∧ (y = z)) ↔ ¬(¬(x =y) ∨ (¬(y = z))) := by
  bv_decide

set_option trace.bv true in
theorem substructure_unit_1' (x y z : BitVec 8) : ((x = y) && (y = z)) ↔ ¬(¬(x = y) || (!(y = z))) := by
  bv_decide

set_option trace.bv true in
theorem substructure_unit_1'' (x y z : BitVec 8) : (Bool.and (x = y) (y = z)) ↔ ¬(Bool.or (!(x = y)) (Bool.not (y = z))) := by
  bv_decide

set_option trace.bv true in
theorem substructure_unit_2 (x y : BitVec 8) : x = y → y = x := by
  bv_decide

set_option trace.bv true in
theorem substructure_unit_3 (x y : BitVec 8) : xor (x = y) (y ≠ x) := by
  bv_decide

set_option trace.bv true in
theorem substructure_unit_3' (x y : BitVec 8) : Bool.xor (x = y) (y ≠ x) := by
  bv_decide
