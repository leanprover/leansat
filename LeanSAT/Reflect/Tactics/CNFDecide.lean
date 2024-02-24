/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.Tactics.Reflect
import LeanSAT.Reflect.CNF.Decidable -- This import is not used directly, but without it the tactic fails.
import LeanSAT.Reflect.BoolExpr.Tseitin.Lemmas

open Lean Meta ReflectSat

/--
Interface for an external SAT solver with a verified certificate checker.

The type `β` representing the unsatisfiability certificate should have `ToExpr β`,
because we will need to embed the certificate in the generated proof.
-/
structure Solver (β : Type) where
  /-- An IO function that retrieves an opaque certificate of type `β`. -/
  runExternal : CNF Nat → IO β
  /--
  A verification function,
  where `verify c b = true` if `b` is a valid certificate of the unsatisfiability of `c`.
  -/
  verify : CNF Nat → β → Bool
  /-- Proof of the correctness of the verification function. -/
  correct : ∀ c b, verify c b = true → c.unsat

/--
We can lift a `Solver β` to a function `CNF Nat → MetaM Expr`,
which given `x : CNF Nat` produces a proof of `x.unsat`.

But we need to jump through some hoops!
-/
def Solver.lift (solverName : Name) (certType : Expr) [ToExpr β] (s : Solver β) (c : CNF Nat) :
    MetaM Expr := do
  let b ← s.runExternal c
  return mkApp5 (.const ``Solver.correct []) certType
    (.const solverName []) (toExpr c) (toExpr b) (← mkEqRefl (toExpr true))

-- We can solve *very* small problems by decidability.
def byDecideSolver : Solver Unit where
  runExternal _ := pure ()
  verify c _ := decide c.unsat
  correct _ _ := of_decide_eq_true

def byDecideSolver' : CNF Nat → MetaM Expr :=
  Solver.lift ``byDecideSolver (.const ``Unit []) byDecideSolver

def _root_.Lean.MVarId.cnfDecide (g : MVarId) : MetaM Unit := M.run do
  let g' ← falseOrByContra g
  g'.withContext do
    let (boolExpr, f) ← reflectSAT g'
    trace[sat] "Reflected boolean expression: {boolExpr}"
    let cnf := boolExpr.toCNF
    trace[sat] "Converted to CNF: {cnf}"
    let cnfUnsat ← byDecideSolver' cnf
    let unsat := mkApp2 (.const ``BoolExpr.unsat_of_toCNF_unsat []) (toExpr boolExpr) cnfUnsat
    g'.assign (← f unsat)

syntax (name := cnfDecideSyntax) "cnf_decide" : tactic

open Elab.Tactic
elab_rules : tactic
  | `(tactic| cnf_decide) => do liftMetaFinishingTactic fun g => g.cnfDecide
