/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.Tactics.Reflect
import LeanSAT.Reflect.CNF.Decidable -- This import is not used directly, but without it the tactic fails.
import LeanSAT.Reflect.BoolExpr.Tseitin

open Lean Meta ReflectSat

/--
Interface for an external SAT solver with a verified certificate checker.

The type `α` representing the specific encoding of `CNF Nat` that the `Solver`
backend uses.

The type `β` representing the unsatisfiability certificate should have `ToExpr β`,
because we will need to embed the certificate in the generated proof.
-/
structure Solver (α : Type) (β : Type) where
  /-- Encode the generic `CNF Nat` into the `Solver` specific CNF format. -/
  encodeCNF : CNF Nat → α
  /-- An IO function that retrieves an opaque certificate of type `β`. -/
  runExternal : α → IO β
  /--
  A verification function,
  where `verify (encodeCNF c) b = true` if `b` is a valid certificate of the unsatisfiability of `c`.
  -/
  verify : α → β → Bool
  /-- Proof of the correctness of the verification function. -/
  correct : ∀ c b, verify (encodeCNF c) b = true → c.unsat

/--
We can lift a `Solver β` to a function `CNF Nat → MetaM Expr`,
which given `x : CNF Nat` produces a proof of `x.unsat`.

But we need to jump through some hoops!
-/
def Solver.lift (solverName : Name) (cnfType : Expr) (certType : Expr) [ToExpr β] (s : Solver α β) (c : CNF Nat) :
    MetaM Expr := do
  let encoded := s.encodeCNF c
  let b ← s.runExternal encoded
  -- TODO: fix
  return mkApp6 (.const ``Solver.correct []) cnfType certType
    (.const solverName []) (toExpr c) (toExpr b) (← mkEqRefl (toExpr true))

-- We can solve *very* small problems by decidability.
def byDecideSolver : Solver (CNF Nat) Unit where
  encodeCNF := id
  runExternal _ := pure ()
  verify c _ := decide c.unsat
  correct _ _ := of_decide_eq_true

def byDecideSolver' : CNF Nat → MetaM Expr :=
  Solver.lift ``byDecideSolver (mkApp (mkConst ``CNF) (mkConst ``Nat)) (.const ``Unit []) byDecideSolver

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
