import LeanSAT.Reflect.Tactics.SatDecide
import LeanSAT.Reflect.Tactics.CNFDecide

example (h : true = false) : False := by sat_decide
example {x y z : Bool} (_ : (x && y) = z) (_ : x = !y) (_ : z = true) : False := by sat_decide
example {a b c d e f : Bool} (_ : (a && b) = c) (_ : (b && c) = d) (_ : (c && d) = e) (_ : (d && e) = f)
    (_ : a = false) (_ : f = true) : False := by sat_decide


-- We are quite profligate with variables when doing the Tseitin transform to CNF.
-- A SAT solver won't care, but case bashing very much does!
-- So we can't test much for now.
example (h : true = false) : False := by cnf_decide
example (h : x = false) : false = x := by cnf_decide
example (_ : x = true) (_ : (x && false) = true) : False := by cnf_decide
