import LeanSAT.External.Solver
import LeanSAT.LRAT.LRATChecker
import LeanSAT.LRAT.LRATCheckerSound
import LeanSAT.External.LRAT

open Dimacs LRAT

def main : List String → IO Unit := fun args => do
  let problemFileOpt : Option String := args[0]?
  let prfFileOpt : Option String := args[1]?
  match problemFileOpt, prfFileOpt with
  | some problemFile, some prfFile =>
    match ← parseProblem problemFile with
    | some ⟨n, formula⟩ =>
      let h ← IO.FS.Handle.mk prfFile IO.FS.Mode.read
      let mut formula : DefaultFormula n := Formula.ofArray formula
      let mut res : LRAT.Result := LRAT.Result.out_of_proof
      let mut encounteredParsingError := false
      while !encounteredParsingError && res == LRAT.Result.out_of_proof do
        let line ← h.getLine
        if line.isEmpty then
          encounteredParsingError := true
          IO.println "LRAT proof terminated without adding the empty clause"
          break
        else if line.startsWith "c" then
          continue -- Skip over comments
        else
          match ← lineToAction line with
          | some intAction =>
            match ← intActionToDefaultClauseActionIO n intAction with
            | some action => (formula, res) := incrementalLRATChecker formula action
            | none => encounteredParsingError := true; break
          | none => encounteredParsingError := true; break
      if encounteredParsingError then IO.println "Error while parsing LRAT proof"
      else if res == LRAT.Result.rup_failure then IO.println "Failed to validate LRAT proof"
      else IO.println "Succeeded in validating LRAT proof"
    | none => IO.println "Unable to parse the problem file"
  | _, _ => IO.println "Requires two arguments [problem file] [proof file]"

#eval main ["./pigeon-hole/hole6.cnf", "./pigeon-hole/hole6.lrat"]
#eval main ["./pigeon-hole/hole7.cnf", "./pigeon-hole/hole7.lrat"]