import LeanSAT.Reflect.Tactics.BVTrace

open BitVec

/--
info: Try this: by_contra;
  simp only [BVDecide.Normalize.BitVec.eq_to_beq, BVDecide.Normalize.Bool.ne_to_beq, Bool.beq_true] at *;
  bv_check "Trace.lean-trace_unit_1-12-2.lrat"
-/
#guard_msgs in
theorem trace_unit_1 (x y : BitVec 64) : x + y = y + x := by
  bv_decide?

/--
info: Try this: by_contra;
  simp only [BVDecide.Normalize.BitVec.eq_to_beq, beq_self_eq_true', BVDecide.Normalize.Bool.ne_to_beq,
    Bool.not_true] at *
-/
#guard_msgs in
theorem trace_unit_2 (x : BitVec 64) : x = x := by
  bv_decide?

theorem trace_unit_1' (x y : BitVec 64) : x + y = y + x := by
  by_contra;
    simp only [BVDecide.Normalize.BitVec.eq_to_beq, BVDecide.Normalize.Bool.ne_to_beq,
      Bool.beq_true] at *;
    bv_check "trace.lrat"

theorem trace_unit_2' (x : BitVec 64) : x = x := by
  by_contra;
    simp only [BVDecide.Normalize.BitVec.eq_to_beq, beq_self_eq_true',
      BVDecide.Normalize.Bool.ne_to_beq, Bool.not_true] at *
