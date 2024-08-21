import Std.Tactic.BVDecide

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
  bv_check "Trace.lean-trace_unit_1-8-2.lrat"

theorem trace_unit_2' (x : BitVec 64) : x = x := by
  bv_normalize

/--
info: Try this: bv_normalize
---
error: This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around.
-/
#guard_msgs in
theorem trace_unit_3 (x : BitVec 64) : x = x := by
  bv_check "foo.lrat"
