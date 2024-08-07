import LeanSAT.LRAT.LRATChecker

open LRAT Lean Parser Elab Command Dimacs Std Sat

open Lean Parser Elab Command

/-- Since `IntAction` is a convenient parsing target and `DefaultClauseAction` is a useful Action type for working with default
    clauses, an expected workflow pattern is to parse an external LRAT proof into a list of `IntAction`s, and then use this function
    to convert that list of `IntAction`s to `DefaultClauseAction`s.

    This function throws an error if any of the literals in the `IntAction` are 0 or ≥ n. -/
def intActionToDefaultClauseActionCommand (n : Nat) : IntAction → CommandElabM (DefaultClauseAction n)
  | .addEmpty cId rupHints => return .addEmpty cId rupHints
  | .addRup cId c rupHints => do
    let c : Array (Option (Literal (PosFin n))) :=
      c.map (fun x => if h : x ≠ 0 then intToLiteralPure x h else none)
    if c.contains none then
      throwError "Failed to convert at least one literal in {c}"
    else
      let c := c.filterMap id
      match Clause.ofArray c with
      | none => throwError "Clause {c} contains complementary literals"
      | some c => return .addRup cId c rupHints
  | .addRat cId c pivot rupHints ratHints => do
    if h : pivot.1 ≠ 0 then
      let some pivot := natLiteralToPosFinLiteral pivot h
        | throwError "Failed to turn {pivot} to a literal"
      let c : Array (Option (Literal (PosFin n))) :=
        c.map (fun x => if h : x ≠ 0 then intToLiteralPure x h else none)
      if c.contains none then
        throwError "Failed to convert at least one literal in {c}"
      else
        let c := c.filterMap id
        match Clause.ofArray c with
        | none => throwError "Clause {c} contains complementary literals"
        | some c => return .addRat cId c pivot rupHints ratHints
    else
      throwError "pivot cannot be 0"
  | .del ids => return .del ids

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
      let proof ← proof.mapM $ intActionToDefaultClauseActionCommand n
      IO.println s!"lratChecker output: {lratChecker formula proof.toList}"
    | _, _ => throwError "Either {problemFile} or {prfFile} did not register as a string literal"
  | _ => throwError "Failed to parse loadLRAT command"

lratCheck "./pigeon-hole/hole6.cnf" "./pigeon-hole/hole6.lrat"
