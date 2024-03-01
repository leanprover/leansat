import LeanSAT.Reflect.Tactics.SatDecide
import LeanSAT.Reflect.Tactics.SatCheck
import LeanSAT.Reflect.Tactics.SatTrace
import Std.Tactic.GuardMsgs

/-- info: Try this: sat_check "Sat.lean-test-8-47.lrat" -/
#guard_msgs in
theorem test (h : x = false) : false = x := by sat_decide?

example (h : true = false) : False := by sat_decide
example {x y z : Bool} (_ : (x && y) = z) (_ : x = !y) (_ : z = true) : False := by sat_decide
example {a b c d e f : Bool} (_ : (a && b) = c) (_ : (b && c) = d) (_ : (c && d) = e) (_ : (d && e) = f)
    (_ : a = false) (_ : f = true) : False := by sat_decide

example (h : true = false) : False := by sat_decide
example (h : x = false) : false = x := by sat_decide
example (h : x = false) : false = x := by sat_check "sat_check.lrat"


def axiomCheck (_ : x = true) (_ : (x && false) = true) : False := by sat_decide

/--
info: 'axiomCheck' depends on axioms: [propext, Classical.choice, Quot.sound, Lean.ofReduceBool]
-/
#guard_msgs in
#print axioms axiomCheck

set_option pp.all true
#print axiomCheck
