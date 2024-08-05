/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Tactics.Glue
import LeanSAT.Tactics.Attr
import LeanSAT.LRAT.LRATChecker
import LeanSAT.LRAT.LRATCheckerSound
import LeanSAT.LRAT.Trim
import LeanSAT.External.Solver

open Lean Elab Meta Sat

namespace BVDecide

/--
The context for the `bv_decide` tactic.
-/
structure TacticContext where
  exprDef : Name
  certDef : Name
  reflectionDef : Name
  solver : String
  lratPath : System.FilePath
  graphviz : Bool
  timeout : Nat
  trimProofs : Bool

def TacticContext.new (lratPath : System.FilePath) : Lean.Elab.TermElabM TacticContext := do
  let exprDef ← Lean.Elab.Term.mkAuxName `_expr_def
  let certDef ← Lean.Elab.Term.mkAuxName `_cert_def
  let reflectionDef ← Lean.Elab.Term.mkAuxName `_reflection_def
  let solver := sat.solver.get (← getOptions)
  let timeout := sat.timeout.get (← getOptions)
  let graphviz := bv.graphviz.get (← getOptions)
  let trimProofs := bv.trimProofs.get (← getOptions)
  return { exprDef, certDef, reflectionDef, solver, lratPath, graphviz, timeout, trimProofs }

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
      mkApp5 (mkConst ``LRAT.Action.addRup [.zero, .zero])
        beta
        alpha
        (toExpr id)
        (toExpr c)
        (toExpr hints)
    | .addRat id c pivot rupHints ratHints =>
      mkApp7 (mkConst ``LRAT.Action.addRat [.zero, .zero])
        beta
        alpha
        (toExpr id)
        (toExpr c)
        (toExpr pivot)
        (toExpr rupHints)
        (toExpr ratHints)
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

def withTempFile [Monad m] [MonadFinally m] [MonadLiftT IO m] (f : System.FilePath → m α)
    : m α := do
  let file ← mkTemp
  try
    f file
  finally
    IO.FS.removeFile file

def LratCert.ofFile (lratPath : System.FilePath) (trimProofs : Bool) : MetaM LratCert := do
  let proofInput ← LRAT.readFileQuick lratPath
  let proof ←
    withTraceNode `sat (fun _ => return s!"Parsing LRAT file") do
      -- lazyPure to prevent compiler lifting
      let proof? ← IO.lazyPure (fun _ => LRAT.parseLRATProof proofInput)
      match proof? with
      | some proof => pure proof
      | none => throwError "SAT solver produced invalid LRAT"

  trace[sat] s!"LRAT proof has {proof.size} steps before trimming"

  let proof ←
    if trimProofs then
      withTraceNode `sat (fun _ => return "Trimming LRAT proof") do
        LRAT.trim proof
    else
      pure proof

  trace[sat] s!"LRAT proof has {proof.size} steps after trimming"

  -- This is necessary because the proof might be in the binary format in which case we cannot
  -- store it as a string in the environment (yet) due to missing support for binary literals.
  let newProof := LRAT.lratProofToString proof
  return newProof

/--
Run an external SAT solver on the `LratFormula` to obtain an LRAT proof.

This will obtain an `LratCert` if the formula is UNSAT and throw errors otherwise.
-/
def runExternal (formula : LratFormula) (solver : String) (lratPath : System.FilePath)
    (trimProofs : Bool) (timeout : Nat) : MetaM (Except (Array (Bool × Nat)) LratCert) := do
  withTempFile fun cnfPath => do
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
        LratCert.ofFile lratPath trimProofs

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

theorem verifyCert_correct
    : ∀ cnf cert, verifyCert (LratFormula.ofCnf cnf) cert = true → unsatisfiable Nat cnf := by
  intro c b h1
  dsimp [verifyCert] at h1
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
    replace h2 := (LRAT.unsat_of_cons_none_unsat _ h2) assignment
    intro h3
    apply h2
    simp only [LRAT.Formula.formulaHSat_def, List.all_eq_true, decide_eq_true_eq]
    intro lratClause hlclause
    simp only [LRAT.Formula.toList, LRAT.DefaultFormula.toList, LRAT.DefaultFormula.ofArray,
      CNF.convertLRAT', Array.size_toArray, List.length_map, Array.toList_eq, Array.data_toArray,
      List.map_nil, List.append_nil, List.mem_filterMap, List.mem_map, id_eq, exists_eq_right] at hlclause
    rcases hlclause with ⟨reflectClause, ⟨hrclause1, hrclause2⟩⟩
    simp only [(· ⊨ ·), CNF.eval, List.all_eq_true] at h3
    split at hrclause2
    . next heq =>
      rw [← heq] at hrclause2
      simp only [Option.some.injEq] at hrclause2
      simp [CNF.Clause.convertLRAT_sat_of_sat reflectClause hrclause2, h3 reflectClause hrclause1]
    . contradiction
  . contradiction

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


end BVDecide
