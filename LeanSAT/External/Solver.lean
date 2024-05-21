/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.External.LRAT
import Lean.Data.Parsec

open Lean Parsec
open IO.Process

inductive SolverResult where
| sat (assignment : Array (Bool × Nat))
| unsat

namespace SatWitnessParser

def parsePartialAssignment : Parsec (Bool × (Array (Bool × Nat))) := do
  skipString "v "
  let idents ← many1 LRAT.Parser.parseClause.litWs
  let idents := idents.map (fun i => if i > 0 then (true, i.toNat) else (false, i.toNat))
  if (← peek!) == '0' then
    return (true, idents)
  else
    return (false, idents)

partial def parseLines : Parsec (Array (Bool × Nat)) :=
  go #[]
where
  go (acc : Array (Bool × Nat)) : Parsec (Array (Bool × Nat)) := do
    let (terminal?, additionalAssignment) ← parsePartialAssignment
    let acc := acc ++ additionalAssignment
    if terminal? then
      return acc
    else
      go acc

def parseHeader : Parsec Unit :=
  skipString "s SATISFIABLE\n"

def parse : Parsec (Array (Bool × Nat)) := do
  parseHeader
  parseLines

end SatWitnessParser

/-- By default, satQuery assumes that the user has cadical (≥ version 1.7.0) installed and their path set up so that it
    can be run via the command `cadical` in terminal. If the path to the user's `cadical` is different, it can be provided
    in the `solverPath` argument. `satQuery` will call cadical on the CNF file at `problemPath` and output an LRAT result
    to `proofOutput` -/
def satQuery (solverPath := "cadical") (problemPath : System.FilePath) (proofOutput : System.FilePath) : IO SolverResult := do
  let cmd := solverPath
  let args := #[problemPath.toString, proofOutput.toString, "--lrat", "--no-binary", "--quiet"]
  let out ← output ⟨⟨Stdio.inherit, Stdio.inherit, Stdio.inherit⟩, cmd, args, none, #[], false⟩
  if out.exitCode == 255 then
    throw <| IO.userError s!"Failed to execute external prover:\n{out.stderr}"
  else
    let stdout := out.stdout
    if stdout.startsWith "s UNSATISFIABLE" then
      return .unsat
    else if stdout.startsWith "s SATISFIABLE" then
      match SatWitnessParser.parse.run stdout with
      | .ok assignment => return .sat assignment
      | .error err =>
        throw <| IO.userError s!"Error {err} while parsing:\n{stdout}"
    else
      throw <| IO.userError s!"The external prover produced unexpected output:\n{stdout}"
