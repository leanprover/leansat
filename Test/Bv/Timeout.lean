import LeanSAT.Reflect.Tactics.BVDecide

open BitVec

/--
error: The SAT solver timed out while solving the problem.
Consider increasing the timeout with `set_option sat.timeout <sec>`
-/
#guard_msgs in
set_option sat.timeout 1 in
theorem timeout (x y : BitVec 2048) : x + y = y + x := by
  bv_decide
