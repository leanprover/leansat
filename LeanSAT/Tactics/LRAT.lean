/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Tactics.Attr
import LeanSAT.LRAT.Checker
import LeanSAT.LRAT.Trim
import LeanSAT.External.Solver

namespace Std
namespace Sat

def Literal.dimacs' (lit : Literal Nat) : String :=
  let ⟨id, pol⟩ := lit
  let id := id + 1 -- DIMACS does not allow 0 as identifier

  if pol then
    s!"{id}"
  else
    s!"-{id}"

namespace CNF

def Clause.dimacs (clause : Clause Nat) : String :=
  clause.foldl (init := "") (· ++ ·.dimacs' ++ " ") ++ "0"

def dimacs (cnf : CNF Nat) : String :=
  let numClauses := cnf.length
  let maxIdentifier := (cnf.maxLiteral |>.getD 0) + 1
  let base := s!"p cnf {maxIdentifier} {numClauses}\n"
  cnf.foldl (init := base) (· ++ ·.dimacs ++ "\n")

end CNF
end Sat
end Std

namespace LeanSAT
namespace BVDecide

open Lean Elab Meta Std Sat

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
  binaryProofs : Bool

def TacticContext.new (lratPath : System.FilePath) : Lean.Elab.TermElabM TacticContext := do
  let exprDef ← Lean.Elab.Term.mkAuxName `_expr_def
  let certDef ← Lean.Elab.Term.mkAuxName `_cert_def
  let reflectionDef ← Lean.Elab.Term.mkAuxName `_reflection_def
  let opts ← getOptions
  let solver := sat.solver.get opts
  let timeout := sat.timeout.get opts
  let graphviz := bv.graphviz.get opts
  let trimProofs := sat.trimProofs.get opts
  let binaryProofs := sat.binaryProofs.get opts
  return {
    exprDef,
    certDef,
    reflectionDef,
    solver,
    lratPath,
    graphviz,
    timeout,
    trimProofs,
    binaryProofs
  }

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
  let proofInput ← IO.FS.readBinFile lratPath
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
Run an external SAT solver on the `CNF` to obtain an LRAT proof.

This will obtain an `LratCert` if the formula is UNSAT and throw errors otherwise.
-/
def runExternal (cnf : CNF Nat) (solver : String) (lratPath : System.FilePath)
    (trimProofs : Bool) (timeout : Nat) (binaryProofs : Bool)
    : MetaM (Except (Array (Bool × Nat)) LratCert) := do
  withTempFile fun cnfPath => do
    withTraceNode `sat (fun _ => return "Serializing SAT problem to DIMACS file") do
      -- lazyPure to prevent compiler lifting
      IO.FS.writeFile cnfPath (← IO.lazyPure (fun _ => cnf.dimacs))

    let res ←
      withTraceNode `sat (fun _ => return "Running SAT solver") do
        satQuery solver cnfPath lratPath timeout binaryProofs
    if let .sat assignment := res then
      return .error assignment

    let lratProof ←
      withTraceNode `sat (fun _ => return "Obtaining LRAT certificate") do
        LratCert.ofFile lratPath trimProofs

    return .ok lratProof

/--
Verify that a proof certificate is valid for a given formula.
-/
def verifyCert (cnf : CNF Nat) (cert : LratCert) : Bool :=
  match LRAT.parseLRATProof cert.toUTF8 with
  | some lratProof => LRAT.check lratProof cnf
  | none => false

theorem verifyCert_correct
    : ∀ cnf cert, verifyCert cnf cert = true → cnf.Unsat := by
  intro c b h1
  unfold verifyCert at h1
  split at h1
  . apply LRAT.check_sound
    assumption
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
end LeanSAT
