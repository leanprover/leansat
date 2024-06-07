/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.External.LRAT
import Lean.Data.Parsec

open IO.Process

inductive SolverResult where
| sat (assignment : Array (Bool × Nat))
| unsat

namespace SatWitnessParser

open LRAT Parsec Byte

def parsePartialAssignment : Parsec ByteArray.Iterator (Bool × (Array (Bool × Nat))) := do
  skipChar 'v'
  let idents ← many (attempt wsLit)
  let idents := idents.map (fun i => if i > 0 then (true, i.natAbs) else (false, i.natAbs))
  Parsec.tryCatch
    (skipString " 0")
    (csuccess := fun _ => pure (true, idents))
    (cerror := fun _ => do
      skipChar '\n'
      return (false, idents)
    )
where
  @[inline]
  wsLit : Parsec ByteArray.Iterator Int := do
    skipChar ' '
    let lit ← LRAT.Parser.parseLit
    return lit

partial def parseLines : Parsec ByteArray.Iterator (Array (Bool × Nat)) :=
  go #[]
where
  go (acc : Array (Bool × Nat)) : Parsec ByteArray.Iterator (Array (Bool × Nat)) := do
    let (terminal?, additionalAssignment) ← parsePartialAssignment
    let acc := acc ++ additionalAssignment
    if terminal? then
      return acc
    else
      go acc

def parseHeader : Parsec ByteArray.Iterator Unit := do
  skipString "s SATISFIABLE\n"

/--
Parse the witness format of a SAT solver. The rough grammar for this is:
line = "v" (" " lit)* (" " 0)?\n
witness = "s SATISFIABLE\n" line+
-/
def parse : Parsec ByteArray.Iterator (Array (Bool × Nat)) := do
  parseHeader
  parseLines

end SatWitnessParser

/-- By default, satQuery assumes that the user has cadical (≥ version 1.7.0) installed and their path set up so that it
    can be run via the command `cadical` in terminal. If the path to the user's `cadical` is different, it can be provided
    in the `solverPath` argument. `satQuery` will call cadical on the CNF file at `problemPath` and output an LRAT result
    to `proofOutput` -/
def satQuery (solverPath := "cadical") (problemPath : System.FilePath) (proofOutput : System.FilePath)
    (timeout : Nat) : IO SolverResult := do
  let cmd := solverPath
  let args := #[
    problemPath.toString,
    proofOutput.toString,
    "-t",
    s!"{timeout}",
    "--lrat",
    "--no-binary",
    "--quiet",
    "--unsat" -- This sets the magic parameters of cadical to optimize for UNSAT search.
  ]
  let out ← output ⟨⟨Stdio.inherit, Stdio.inherit, Stdio.inherit⟩, cmd, args, none, #[], false⟩
  if out.exitCode == 255 then
    throw <| IO.userError s!"Failed to execute external prover:\n{out.stderr}"
  else
    let stdout := out.stdout
    if stdout.startsWith "s UNSATISFIABLE" then
      return .unsat
    else if stdout.startsWith "s SATISFIABLE" then
      match SatWitnessParser.parse.run <| .fresh stdout.toUTF8 with
      | .ok assignment =>
        return .sat assignment
      | .error err =>
        throw <| IO.userError s!"Error {err} while parsing:\n{stdout}"
    else if stdout.startsWith "c UNKNOWN" then
      let mut err := "The SAT solver timed out while solving the problem."
      err := err ++ "\nConsider increasing the timeout with `set_option sat.timeout <sec>`"
      throw <| IO.userError err
    else
      throw <| IO.userError s!"The external prover produced unexpected output:\n{stdout}"
