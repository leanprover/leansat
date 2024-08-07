/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import Lean.Elab.Command
import LeanSAT.LRAT.Clause

open LRAT Lean Parser Elab Command DefaultClause Std.Sat

namespace Dimacs

def intToLiteral [Monad m] [MonadError m] {n : Nat} (x : Int) (x_ne_zero : x ≠ 0)
    : m (Literal (PosFin n)) :=
  if h : x.natAbs < n then
    if x > 0 then
      return (⟨x.natAbs, ⟨by omega, h⟩⟩, true)
    else
      return (⟨x.natAbs, ⟨by omega, h⟩⟩, false)
  else
    throwError "Given literal {x} is outside of the bounds specified by the number of variables"

/--
`loadProblem` takes in the path of a CNF file and attempts to output a number `n` (indicating the total number
of variables + 1) along with an Array of `DefaultClause n` Option expressions. This Array should match the
`ofArray` specification given in `Formula.Implementation.lean`.
-/
def loadProblem (path : System.FilePath) [Monad m] [MonadError m] [MonadLiftT IO m]
    : m (Σ n : Nat, Array (Option (DefaultClause n))) := do
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
        | none =>
          throwError "Dimacs requires that no clause contain a complementary set of literals"
      else
        res := res.push curClause
        curClause := empty -- Reset curClause because the 0 just terminated the previous clause
  if curClause.clause ≠ [] then -- Dimacs format allows the last clause to not terminate in a 0
    res := res.push curClause
  if res.size != numClauses + 1 then
    throwError
      "The problem line stated there were {numClauses} clauses but there are actually {res.size}"
  return ⟨numVarsSucc, res⟩

def intToLiteralPure {n : Nat} (x : Int) (x_ne_zero : x ≠ 0) : Option (Literal (PosFin n)) := do
  if h : x.natAbs < n then
    if x > 0 then some (⟨x.natAbs, ⟨by omega, h⟩⟩, true)
    else some (⟨x.natAbs, ⟨by omega, h⟩⟩, false)
  else
    none
