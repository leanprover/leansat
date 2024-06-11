/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Henrik Böving
-/
import Lean.Elab.Tactic.FalseOrByContra
import LeanSAT.Reflect.Tactics.Reflect
import LeanSAT.Reflect.Glue

import LeanSAT.AIG.CNF
import LeanSAT.AIG.BoolExprCached

import LeanSAT.LRAT.LRATChecker
import LeanSAT.LRAT.LRATCheckerSound
import LeanSAT.External.Solver

open Lean Elab Meta ReflectSat

namespace SatDecide

/--
The context for the `sat_decide` tactic.
-/
structure TacticContext where
  exprDef : Name
  certDef : Name
  reflectionDef : Name
  solver : String
  lratPath : System.FilePath
  prevalidate : Bool
  timeout : Nat

/--
A wrapper type for `LRAT.DefaultFormula`. We use it to hide the `numVars` parameter.
-/
structure LratFormula where
  /-- Number of variables in `formula`. -/
  {numVars : Nat}
  /-- The actual SAT formula in the LeanSAT framework. -/
  formula : LRAT.DefaultFormula numVars.succ

/-- An LRAT proof read from a file. This will get parsed using ofReduceBool. -/
abbrev LratCert := String

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


/--
Turn a `CNF` from the reflection framework into the correct format for the LRAT framework.
-/
def LratFormula.ofCnf (cnf : CNF Nat) : LratFormula := ⟨cnf.convertLRAT⟩

/--
Create a temporary file using `mktemp` and return the path to it.
-/
def mkTemp : IO System.FilePath := do
  let out ← IO.Process.output { cmd := "mktemp" }
  return out.stdout.trim

/--
A quicker version of `IO.FS.readFile` for big files. Note that this assumes the file contains valid
UTF-8. As we only use this to parse trusted input from a SAT solver this is fine.
-/
def readFileQuick (path : System.FilePath) : IO ByteArray := do
  let mdata ← path.metadata
  let handle ← IO.FS.Handle.mk path .read
  handle.read mdata.byteSize.toUSize

def LratCert.ofFile (lratPath : System.FilePath) (prevalidate : Bool) : IO LratCert := do
  let proof ← readFileQuick lratPath
  -- This is just a sanity check to verify that the proof does indeed parse.
  -- The parsing relevant for the reflection proof happens in the reflection term.
  -- As parsing can be expensive this is configured through a default-disabled option.
  if prevalidate then
    if LRAT.parseLRATProof proof |>.isNone then
      throw <| IO.userError "SAT solver produced invalid LRAT"
  return String.fromUTF8! proof

/--
Run an external SAT solver on the `LratFormula` to obtain an LRAT proof.

This will obtain an `LratCert` if the formula is UNSAT and throw errors otherwise.
-/
def runExternal (formula : LratFormula) (solver : String) (lratPath : System.FilePath)
    (prevalidate : Bool) (timeout : Nat) : MetaM (Except (Array (Bool × Nat)) LratCert) := do
  let cnfPath ← mkTemp
  withTraceNode `sat (fun _ => return "Serializing SAT problem to DIMACS file") do
    -- lazyPure to prevent compiler lifting
    IO.FS.writeFile cnfPath (← IO.lazyPure (fun _ => formula.formula.dimacs))

  let res ←
    withTraceNode `sat (fun _ => return "Running SAT solver") do
      satQuery solver cnfPath lratPath timeout
  if let .sat assignment := res then
    return .error assignment

  let lratProof ←
    withTraceNode `sat (fun _ => return "Obtaining LRAT certificate") do
      LratCert.ofFile lratPath prevalidate

  -- cleanup files such that we don't pollute /tmp
  IO.FS.removeFile cnfPath
  return .ok lratProof

/--
Verify that a proof certificate is valid for a given formula.
-/
def verifyCert (formula : LratFormula) (cert : LratCert) : Bool :=
  match LRAT.parseLRATProof cert.toUTF8 with
  | some lratProof =>
    -- XXX
    let lratProof := lratProof.toList
    let lratProof := lratProof.map (LRAT.intActionToDefaultClauseAction formula.numVars.succ)
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
    checkerResult = .success
  | none => false

theorem verifyCert_correct : ∀ cnf cert, verifyCert (LratFormula.ofCnf cnf) cert = true → cnf.unsat := by
  intro c b h1
  dsimp[verifyCert] at h1
  split at h1
  . simp only [decide_eq_true_eq] at h1
    have h2 :=
      lratCheckerSound
        _
        (by apply CNF.convertLRAT_readfyForRupAdd)
        (by apply CNF.convertLRAT_readfyForRatAdd)
        _
        (by
          intro action h
          simp only [List.mem_map, List.mem_filterMap] at h
          rcases h with ⟨wellFormedActions, _, h2⟩
          rw [← h2]
          exact wellFormedActions.property)
        h1
    apply CNF.unsat_of_lift_unsat c
    intro assignment
    unfold CNF.convertLRAT at h2
    have h2 := (LRAT.unsat_of_cons_none_unsat _ h2) assignment
    apply eq_false_of_ne_true
    intro h3
    apply h2
    simp only [LRAT.Formula.formulaHSat_def, List.all_eq_true, decide_eq_true_eq]
    intro lratClause hlclause
    simp only [LRAT.Formula.toList, LRAT.DefaultFormula.toList, LRAT.DefaultFormula.ofArray,
      CNF.convertLRAT', Array.size_toArray, List.length_map, Array.toList_eq, Array.data_toArray,
      List.map_nil, List.append_nil, List.mem_filterMap, List.mem_map, id_eq, exists_eq_right] at hlclause
    rcases hlclause with ⟨reflectClause, ⟨hrclause1, hrclause2⟩⟩
    simp only [CNF.eval, List.all_eq_true] at h3
    split at hrclause2
    . next heq =>
      rw [← heq] at hrclause2
      simp only [Option.some.injEq] at hrclause2
      simp [CNF.Clause.convertLRAT_sat_of_sat reflectClause hrclause2, h3 reflectClause hrclause1]
    . contradiction
  . contradiction

/--
Verify that a proof certificate is valid for a given `BoolExpr`.

This is the verification function that we run in the reflection term.
The advantage over running just `verifyCert` is that the Tseitin encoding happens
in the reflection code as well instead of in the kernel reduction engine.
-/
def verifyBoolExpr (b : BoolExprNat) (cert : LratCert) : Bool :=
  verifyCert (LratFormula.ofCnf (AIG.toCNF (AIG.ofBoolExprCachedDirect b.toBoolExpr))) cert

theorem unsat_of_verifyBoolExpr_eq_true (b : BoolExprNat) (c : LratCert)
    (h : verifyBoolExpr b c = true) : BoolExprNat.unsat b := by
  rw [BoolExprNat.unsat_iff]
  rw [← AIG.ofBoolExprCachedDirect_unsat_iff]
  rw [← AIG.toCNF_equisat]
  apply verifyCert_correct
  rw [verifyBoolExpr] at h
  exact h

/--
Add an auxiliary declaration. Only used to create constants that appear in our reflection proof.
-/
def mkAuxDecl (name : Name) (value type : Expr) : MetaM Unit :=
  addAndCompile <| .defnDecl {
    name := name,
    levelParams := [],
    type := type,
    value := value,
    hints := .abbrev,
    safety := .safe
  }

/--
Turn an `LratCert` into a proof that some `reflected` expression is UNSAT by providing a `verifier`
function together with a correctenss theorem for it.

- `verifier` is expected to have type `α → LratCert → Bool`
- `unsat_of_verifier_eq_true` is expected to have type
  `∀ (b : α) (c : LratCert), verifier b c = true → unsat b`
-/
def LratCert.toReflectionProof [ToExpr α] (cert : LratCert) (cfg : TacticContext) (reflected : α)
    (verifier : Name) (unsat_of_verifier_eq_true : Name)
    : MetaM Expr := do
  withTraceNode `sat (fun _ => return "Compiling expr term") do
    mkAuxDecl cfg.exprDef (toExpr reflected) (toTypeExpr α)

  let certType := toTypeExpr LratCert

  withTraceNode `sat (fun _ => return "Compiling proof certificate term") do
    mkAuxDecl cfg.certDef (toExpr cert) certType

  let reflectedExpr := mkConst cfg.exprDef
  let certExpr := mkConst cfg.certDef

  withTraceNode `sat (fun _ => return "Compiling reflection proof term") do
    let auxValue := mkApp2 (mkConst verifier) reflectedExpr certExpr
    mkAuxDecl cfg.reflectionDef auxValue (mkConst ``Bool)

  let nativeProof :=
    mkApp3
      (mkConst ``Lean.ofReduceBool)
      (mkConst cfg.reflectionDef)
      (toExpr true)
      (← mkEqRefl (toExpr true))
  return mkApp3 (mkConst unsat_of_verifier_eq_true) reflectedExpr certExpr nativeProof

/--
Prepare an `Expr` that proves `boolExpr.unsat` using `ofReduceBool`.
-/
def lratSolver (cfg : TacticContext) (boolExpr : BoolExprNat) : MetaM Expr := do
  let cnf ←
    withTraceNode `sat (fun _ => return "Converting BoolExpr to CNF") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ => AIG.toCNF (AIG.ofBoolExprCachedDirect boolExpr.toBoolExpr))

  let encoded ←
    withTraceNode `sat (fun _ => return "Converting frontend CNF to solver specific CNF") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ => LratFormula.ofCnf cnf)

  trace[sat] s!"CNF has {encoded.formula.clauses.size} clauses"

  let res ←
    withTraceNode `sat (fun _ => return "Obtaining external proof certificate") do
      runExternal encoded cfg.solver cfg.lratPath cfg.prevalidate cfg.timeout

  match res with
  | .ok cert =>
    cert.toReflectionProof cfg boolExpr ``verifyBoolExpr ``unsat_of_verifyBoolExpr_eq_true
  | .error _ =>
    throwError "The external prover found a counter example"


def _root_.Lean.MVarId.closeWithBoolReflection (g : MVarId) (unsatProver : BoolExprNat → MetaM Expr) : MetaM Unit := M.run do
  let g' ← g.falseOrByContra
  g'.withContext do
    let (boolExpr, f) ←
      withTraceNode `sat (fun _ => return "Reflecting goal into BoolExpr") do
        reflectSAT g'
    trace[sat] "Reflected boolean expression: {boolExpr}"
    let boolExprUnsat ← unsatProver boolExpr
    let proveFalse ← f boolExprUnsat
    g'.assign proveFalse

/--
Close a goal by:
1. Turning it into a SAT problem.
2. Running an external SAT solver on it and obtaining an LRAT proof from it.
3. Verifying the LRAT proof using proof by reflection.
-/
def _root_.Lean.MVarId.satDecide (g : MVarId) (cfg : TacticContext) : MetaM Unit := M.run do
  let unsatProver (exp : BoolExprNat) : MetaM Expr := do
    withTraceNode `sat (fun _ => return "Preparing LRAT reflection term") do
      lratSolver cfg exp
  g.closeWithBoolReflection unsatProver

@[inherit_doc Lean.MVarId.satDecide]
syntax (name := satDecideSyntax) "sat_decide" : tactic

end SatDecide

def SatDecide.TacticContext.new (lratPath : System.FilePath) : TermElabM TacticContext := do
  let exprDef ← Term.mkAuxName `_expr_def
  let certDef ← Term.mkAuxName `_cert_def
  let reflectionDef ← Term.mkAuxName `_reflection_def
  let solver := sat.solver.get (← getOptions)
  let timeout := sat.timeout.get (← getOptions)
  let prevalidate := sat.prevalidate.get (← getOptions)
  return { exprDef, certDef, reflectionDef, solver, lratPath, prevalidate, timeout }

open Elab.Tactic
elab_rules : tactic
  | `(tactic| sat_decide) => do
    let cfg ← SatDecide.TacticContext.new (← SatDecide.mkTemp)
    liftMetaFinishingTactic fun g => g.satDecide cfg
    -- the auto generated lratPath is a temp file that should be removed
    IO.FS.removeFile cfg.lratPath
