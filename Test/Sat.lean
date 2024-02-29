import LeanSAT.Reflect.Tactics.SatDecide
import LeanSAT.Reflect.Tactics.CNFDecide
import Std.Tactic.GuardMsgs

example (h : true = false) : False := by sat_decide
example {x y z : Bool} (_ : (x && y) = z) (_ : x = !y) (_ : z = true) : False := by sat_decide
example {a b c d e f : Bool} (_ : (a && b) = c) (_ : (b && c) = d) (_ : (c && d) = e) (_ : (d && e) = f)
    (_ : a = false) (_ : f = true) : False := by sat_decide

example (h : true = false) : False := by cnf_decide
example (h : x = false) : false = x := by cnf_decide


def axiomCheck (_ : x = true) (_ : (x && false) = true) : False := by cnf_decide

/--
info: 'axiomCheck' depends on axioms: [propext, Classical.choice, Quot.sound, Lean.ofReduceBool]
-/
#guard_msgs in
#print axioms axiomCheck

set_option pp.all true
#print axiomCheck
