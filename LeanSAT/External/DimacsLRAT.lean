/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import Lean.Elab.Command
import LeanSAT.LRAT.Clause

open LRAT Lean Parser Elab Command DefaultClause

namespace Dimacs

theorem natAbs_is_pos_of_ne_zero {x : Int} (x_ne_zero : x ≠ 0) : 0 < Int.natAbs x := by
  unfold Int.natAbs
  split
  . next n =>
    unfold instOfNatInt at x_ne_zero
    simp only [ne_eq, Int.ofNat.injEq] at x_ne_zero
    exact Nat.zero_lt_of_ne_zero x_ne_zero
  . next n => apply Nat.zero_lt_succ

def intToLiteral [Monad M] [MonadError M] {n : Nat} (x : Int) (x_ne_zero : x ≠ 0) : M (Literal (PosFin n)) :=
  if h : x.natAbs < n then
    if x > 0 then return (⟨x.natAbs, ⟨natAbs_is_pos_of_ne_zero x_ne_zero, h⟩⟩, true)
    else return (⟨x.natAbs, ⟨natAbs_is_pos_of_ne_zero x_ne_zero, h⟩⟩, false)
  else throwError "Given literal {x} is outside of the bounds specified by the number of variables"

/-- `loadProblem` takes in the path of a CNF file and attempts to output a number `n` (indicating the total number
    of variables + 1) along with an Array of `DefaultClause n` Option expressions. This Array should match the
    `ofArray` specification given in `Formula.Implementation.lean`.

    `loadProblem` is written as a `CommandElabM` monad so that it can be used in commands such as `loadDimacs` at
    the end of this file. -/
def loadProblem (path : System.FilePath) : CommandElabM (Σ n : Nat, Array (Option (DefaultClause n))) := do
  let lines ← IO.FS.lines path
  let #[problemLine] := lines.filter fun l => l.startsWith "p"
    | throwError "There must be exactly one problem line in the dimacs file"
  let [_, _, numVars, numClauses] := String.splitOn problemLine " "
    | throwError "Improperly formatted problem line"
  let some numVars := String.toNat? numVars
    | throwError "Improperly formatted problem line"
  let some numClauses := String.toNat? numClauses
    | throwError "Improperly formatted problem line"

  let numVarsSucc := numVars + 1

  let lines := lines.filter fun l => not (l.startsWith "c" || l.startsWith "p")
  let mut res : Array (Option (DefaultClause numVarsSucc)) := #[none]
  let mut curClause : DefaultClause numVarsSucc := empty
  for line in lines do
    let line := line.replace "\t" " "
    let c := (line.splitOn " ").toArray
    for lit in c do
      if lit = "" then continue
      let some lit := String.toInt? lit
        | throwError "Clause {c} contains non-int {lit}"
      if h : lit ≠ 0 then
        match curClause.insert (← intToLiteral lit h) with
        | some updatedClause => curClause := updatedClause
        | none => throwError "Dimacs requires that no clause contain a complementary set of literals"
      else
        res := res.push curClause
        curClause := empty -- Reset curClause because the 0 just terminated the previous clause
  if curClause.clause ≠ [] then -- Dimacs format allows the last clause to not terminate in a 0
    res := res.push curClause
  if res.size != numClauses + 1 then
    throwError "The problem line stated there were {numClauses} clauses but there are actually {res.size} (res: {res})"
  return ⟨numVarsSucc, res⟩

def intToLiteralIO {n : Nat} (x : Int) (x_ne_zero : x ≠ 0) : IO (Option (Literal (PosFin n))) := do
  if h : x.natAbs < n then
    if x > 0 then return some (⟨x.natAbs, ⟨natAbs_is_pos_of_ne_zero x_ne_zero, h⟩⟩, true)
    else return some (⟨x.natAbs, ⟨natAbs_is_pos_of_ne_zero x_ne_zero, h⟩⟩, false)
  else
    IO.println "Given literal {x} is outside of the bounds specified by the number of variables"
    return none

/-- `parseProblem` takes in the path of a CNF file and attempts to output a number `n` (indicating the total number
    of variables + 1) along with an Array of `DefaultClause n` Option expressions. This Array should match the
    `ofArray` specification given in Implementation.lean.

    `parseProblem` is written as an `IO` monad so that it can be used in programs such as `main`. Since the `IO` monad
    does not support `throwError` in the way that `CommandElabM` does, `parseProblem` returns `none` where `loadProblem`
    would throw an error. Other than this difference though, `loadProblem` and `parseProblem` are intended to be equivalent. -/
def parseProblem (path : System.FilePath) : IO (Option (Σ n : Nat, Array (Option (DefaultClause n)))) := do
  let lines ← IO.FS.lines path
  let #[problemLine] := lines.filter fun l => l.startsWith "p"
    | IO.println "There must be exactly one problem line in the dimacs file"; return none
  let [_, _, numVars, numClauses] := String.splitOn problemLine " "
    | IO.println "Improperly formatted problem line"; return none
  let some numVars := String.toNat? numVars
    | IO.println "Improperly formatted problem line"; return none
  let some numClauses := String.toNat? numClauses
    | IO.println "Improperly formatted problem line"; return none

  let numVarsSucc := numVars + 1

  let lines := lines.filter fun l => not (l.startsWith "c" || l.startsWith "p")
  let mut res : Array (Option (DefaultClause numVarsSucc)) := #[none]
  let mut curClause : DefaultClause numVarsSucc := empty
  for line in lines do
    let line := line.replace "\t" " "
    let c := (line.splitOn " ").toArray
    for lit in c do
      if lit = "" then continue
      let some lit := String.toInt? lit
        | IO.println s!"Clause {c} contains non-int {lit}"; return none
      if h : lit ≠ 0 then
        let some lit ← intToLiteralIO lit h
          | return none
        match curClause.insert lit with
        | some updatedClause => curClause := updatedClause
        | none => IO.println s!"Dimacs requires that no clause contain a complementary set of literals"; return none
      else
        res := res.push curClause
        curClause := empty -- Reset curClause because the 0 just terminated the previous clause
  if curClause.clause ≠ [] then -- Dimacs format allows the last clause to not terminate in a 0
    res := res.push curClause
  if res.size != numClauses + 1 then
    IO.println s!"The problem line stated there were {numClauses} clauses but there are actually {res.size - 1} (res: {res})"
    return none
  return some ⟨numVarsSucc, res⟩

syntax (name := loadDimacsCommand) "loadDimacs " strLit : command

@[command_elab loadDimacsCommand] def elabLoadDimacs : CommandElab := fun stx => do
  match stx with
  | `(loadDimacs $file) =>
    match Syntax.isStrLit? file with
    | some file =>
        let ⟨numVarsSucc, formula⟩ ← loadProblem file
        let formula := formula.filterMap id
        IO.println s!"numVars: {numVarsSucc - 1}"
        IO.println s!"formula: {formula.map (fun c => c.dimacs)}"
    | _ => throwError "Expected strLit: {file}"
  | _ => throwError "Failed to parse loadDimacs command"

loadDimacs "./SampleDimacs/empty.cnf"
loadDimacs "./SampleDimacs/unit4.cnf"
loadDimacs "./SampleDimacs/false.cnf"
