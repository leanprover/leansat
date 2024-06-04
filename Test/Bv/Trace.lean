import LeanSAT.Reflect.Tactics.BVTrace

open BitVec

/-- info: Try this: bv_check "Trace.lean-trace_unit_1-8-2.lrat" -/
#guard_msgs in
theorem trace_unit_1 (x y : BitVec 64) : x + y = y + x := by
  bv_decide?

/-- info: Try this: bv_normalize -/
#guard_msgs in
theorem trace_unit_2 (x : BitVec 64) : x = x := by
  bv_decide?

theorem trace_unit_1' (x y : BitVec 64) : x + y = y + x := by
  bv_check "trace.lrat"

theorem trace_unit_2' (x : BitVec 64) : x = x := by
  bv_normalize
