import Lean.Elab.Command
import LeanSAT.External.DimacsLRAT

open Lean Parser Elab Command

syntax (name := loadDimacsCommand) "loadDimacs " strLit : command

@[command_elab loadDimacsCommand] def elabLoadDimacs : CommandElab := fun stx => do
  match stx with
  | `(loadDimacs $file) =>
    match Syntax.isStrLit? file with
    | some file =>
        let ⟨numVarsSucc, formula⟩ ← Dimacs.loadProblem file
        let formula := formula.filterMap id
        IO.println s!"numVars: {numVarsSucc - 1}"
        IO.println s!"formula: {formula.map (fun c => c.dimacs)}"
    | _ => throwError "Expected strLit: {file}"
  | _ => throwError "Failed to parse loadDimacs command"

loadDimacs "./SampleDimacs/empty.cnf"
loadDimacs "./SampleDimacs/unit4.cnf"
loadDimacs "./SampleDimacs/false.cnf"
