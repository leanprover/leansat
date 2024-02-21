import LeanSAT.LRAT.LRATChecker

open LRAT Lean Parser Elab Command Dimacs

syntax (name := lratCheckCommand) "lratCheck" strLit strLit : command

@[command_elab lratCheckCommand] def runLRATCheck : CommandElab := fun stx => do
  match stx with
  | `(lratCheck $problemFile $prfFile) =>
    match Syntax.isStrLit? problemFile, Syntax.isStrLit? prfFile with
    | some problemFile, some prfFile =>
      let ⟨n, formula⟩ ← loadProblem problemFile
      let formula : DefaultFormula n := DefaultFormula.ofArray formula
      let proof ← loadLRATProof prfFile
      IO.println s!"formula: {formula.dimacs}\n"
      -- O.println s!"proof: {proof}\n"
      let proof ← proof.mapM $ intActionToDefaultClauseAction n
      IO.println s!"lratChecker output: {lratChecker formula proof.toList}"
    | _, _ => throwError "Either {problemFile} or {prfFile} did not register as a string literal"
  | _ => throwError "Failed to parse loadLRAT command"

lratCheck "./pigeon-hole/hole6.cnf" "./pigeon-hole/hole6.lrat"
lratCheck "./pigeon-hole/hole7.cnf" "./pigeon-hole/hole7.lrat"
