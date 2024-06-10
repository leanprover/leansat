import LeanSAT.Reflect.Tactics.SatDecide
import LeanSAT.Reflect.Tactics.SatCheck
import LeanSAT.Reflect.Tactics.SatTrace

/-- info: Try this: sat_check "Sat.lean-test-7-47.lrat" -/
#guard_msgs in
theorem test (h : x = false) : false = x := by sat_decide?

example (h : true = false) : False := by sat_decide
example {x y z : Bool} (_ : (x && y) = z) (_ : x = !y) (_ : z = true) : False := by sat_decide
example {a b c d e f : Bool} (_ : (a && b) = c) (_ : (b && c) = d) (_ : (c && d) = e) (_ : (d && e) = f)
    (_ : a = false) (_ : f = true) : False := by sat_decide

example (h : true = false) : False := by sat_decide
example (h : x = false) : false = x := by sat_decide
example (h : x = false) : false = x := by sat_check "sat_check.lrat"


theorem sat_axiomCheck (_ : x = true) (_ : (x && false) = true) : False := by sat_decide

/--
info: 'sat_axiomCheck' depends on axioms: [propext, Quot.sound, Classical.choice, Lean.ofReduceBool]
-/
#guard_msgs in
#print axioms sat_axiomCheck

set_option pp.all true
#print sat_axiomCheck
