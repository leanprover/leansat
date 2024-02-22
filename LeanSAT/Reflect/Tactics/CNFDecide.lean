/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.Tactics.Reflect
import LeanSAT.Reflect.CNF.Decidable -- This import is not used directly, but without it the tactic fails.
import LeanSAT.Reflect.BoolExpr.Tseitin

import LeanSAT.LRAT.LRATChecker
import LeanSAT.External.Solver

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
  return mkApp6 (.const ``Solver.correct []) cnfType certType
    (.const solverName []) (toExpr c) (toExpr b) (← mkEqRefl (toExpr true))

/--
A wrapper type for `LRAT.DefaultFormula`. We use it to hide the `numVars` parameter
as the `Solver` framework does not intend for dependent typing like this.
-/
structure LratFormula where
  /-- Number of variables in `formula`. -/
  numVars : Nat
  /-- The actual SAT formula in the LeanSAT framework. -/
  formula : LRAT.DefaultFormula numVars.succ

/--
An LRAT proof certificate. Note that this only contains a list of LRAT actions
that have not yet been internalized to the formats that LeanSAT's LRAT checker uses.
This is done as we need to provide an `ToExpr LratCert` instance, which not easily
possible for proof carrying structures.
-/
structure LratCert where
  /-- The list of LRAT actions to take for the proof. -/
  cert : List LRAT.IntAction

instance : ToExpr LRAT.IntAction where
  toExpr action :=
    let beta := mkApp (mkConst ``Array [.zero]) (mkConst ``Int)
    let alpha := mkConst ``Nat
    match action with
    | .addEmpty id hints =>
      mkApp4 (mkConst ``LRAT.Action.addEmpty [.zero, .zero]) beta alpha (toExpr id) (toExpr hints)
    | .addRup id c hints =>
      mkApp5 (mkConst ``LRAT.Action.addRup [.zero, .zero]) beta alpha (toExpr id) (toExpr c) (toExpr hints)
    | .addRat id c pivot rupHints ratHints =>
      mkApp7 (mkConst ``LRAT.Action.addRat [.zero, .zero]) beta alpha (toExpr id) (toExpr c) (toExpr pivot) (toExpr rupHints) (toExpr ratHints)
    | .del ids =>
      mkApp3 (mkConst ``LRAT.Action.del [.zero, .zero]) beta alpha (toExpr ids)
  toTypeExpr := mkConst ``LRAT.IntAction

instance : ToExpr LratCert where
  toExpr cert := mkApp (mkConst ``LratCert.mk) (toExpr cert.cert)
  toTypeExpr := mkConst ``LratCert

/--
Obtains the maximum variable index used in `cnf`. If the `cnf` is empty return `none`.
-/
def maxVarNum (cnf : CNF Nat) : Option Nat :=
  cnf.filterMap (·.map Prod.fst |>.maximum?) |>.maximum?

/--
Convert a `CNF Nat` with a certain maximum variable number into the `LRAT.DefaultFormula`
format for usage with LeanSAT.

Notably this:
1. Increments all variables as DIMACS variables start at 1 instead of 0
2. Adds a leading `none` clause. This clause *must* be persistet as the LRAT proof
   refers to the DIMACS file line by line and the DIMACS file begins with the
  `p cnf x y` meta instruction.
-/
def convertCNF (maxVar : Nat) (cnf : CNF Nat) : LRAT.DefaultFormula (maxVar + 2) :=
  let numVars := maxVar + 1
  let convertLit (lit : Nat × Bool) (h : lit.fst ≤ maxVar) : _root_.Literal (PosFin numVars.succ) :=
    -- The reflect framework starts counting variables at 0, DIMACS starts at 1 -> increment
    ⟨⟨lit.fst + 1, by omega⟩, lit.snd⟩
  let convertClause clause := LRAT.DefaultClause.ofArray (clause.map (convertLit · sorry) |>.toArray)
  let clauses := cnf.map convertClause
  let clauses := none :: clauses
  LRAT.DefaultFormula.ofArray clauses.toArray

def lratSolver : Solver LratFormula LratCert where
  encodeCNF reflectCnf :=
    match maxVarNum reflectCnf with
    | some maxVar =>
      ⟨_, convertCNF maxVar reflectCnf⟩
    | none =>
      -- TODO: Cadical refuses an input without clauses, figure out what to do here.
      ⟨0, LRAT.DefaultFormula.ofArray #[]⟩

  runExternal formula := do
    let numVars := formula.numVars
    let formula := formula.formula
    -- TODO: how do we choose filenames? Important for parallelism etc.
    let cnfPath : System.FilePath := "/" / "tmp" / "cnf_decide.cnf"
    let lratPath : System.FilePath := "/" / "tmp" / "lrat_decide.lrat"
    IO.FS.writeFile cnfPath <| formula.dimacs
    let _ ← satQuery "cadical" cnfPath.toString lratPath.toString
    let some lratProof ← LRAT.parseLRATProof lratPath.toString | throw <| IO.userError "SAT solver produced invalid LRAT"
    return ⟨lratProof.toList⟩

  verify formula cert :=
    let lratProof := cert.cert.map (LRAT.intActionToDefaultClauseAction formula.numVars.succ)
    let lratProof : List { act // LRAT.wellFormedAction act } :=
      lratProof.filterMap
        (fun actOpt =>
          match actOpt with
          | none => none
          | some (LRAT.Action.addEmpty id rupHints) =>
            some ⟨LRAT.Action.addEmpty id rupHints, by simp only [LRAT.wellFormedAction]⟩
          | some (LRAT.Action.addRup id c rupHints) =>
            some ⟨LRAT.Action.addRup id c rupHints, by simp only [LRAT.wellFormedAction]⟩
          | some (LRAT.Action.del ids) =>
            some ⟨LRAT.Action.del ids, by simp only [LRAT.wellFormedAction]⟩
          | some (LRAT.Action.addRat id c pivot rupHints ratHints) =>
            if h : pivot ∈ LRAT.Clause.toList c then
              some ⟨
                LRAT.Action.addRat id c pivot rupHints ratHints,
                by simp [LRAT.wellFormedAction, LRAT.Clause.limplies_iff_mem, h]
              ⟩
            else
              -- TODO: report this
              none
        )
    let lratProof := lratProof.map Subtype.val
    let checkerResult := LRAT.lratChecker formula.formula lratProof
    dbg_trace checkerResult
    checkerResult = .success

  correct := by
    intro c b h1
    dsimp at h1
    sorry

-- We can solve *very* small problems by decidability.
def byDecideSolver : Solver (CNF Nat) Unit where
  encodeCNF := id
  runExternal _ := pure ()
  verify c _ := decide c.unsat
  correct _ _ := of_decide_eq_true

def byDecideSolver' : CNF Nat → MetaM Expr :=
  Solver.lift ``byDecideSolver (mkApp (mkConst ``CNF) (mkConst ``Nat)) (.const ``Unit []) byDecideSolver

def lratSolver' : CNF Nat → MetaM Expr :=
  Solver.lift ``lratSolver (mkConst ``LratFormula) (mkConst ``LratCert) lratSolver

def _root_.Lean.MVarId.cnfDecide (g : MVarId) : MetaM Unit := M.run do
  let g' ← falseOrByContra g
  g'.withContext do
    let (boolExpr, f) ← reflectSAT g'
    trace[sat] "Reflected boolean expression: {boolExpr}"
    let cnf := boolExpr.toCNF
    trace[sat] "Converted to CNF: {cnf}"
    --let cnfUnsat ← byDecideSolver' cnf
    let cnfUnsat ← lratSolver' cnf
    let unsat := mkApp2 (.const ``BoolExpr.unsat_of_toCNF_unsat []) (toExpr boolExpr) cnfUnsat
    g'.assign (← f unsat)

syntax (name := cnfDecideSyntax) "cnf_decide" : tactic

open Elab.Tactic
elab_rules : tactic
  | `(tactic| cnf_decide) => do liftMetaFinishingTactic fun g => g.cnfDecide
