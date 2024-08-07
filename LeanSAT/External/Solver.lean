/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.External.LRAT
import Lean.CoreM
import Lean.Data.Parsec

inductive SolverResult where
| sat (assignment : Array (Bool × Nat))
| unsat

namespace SatWitnessParser

open LRAT
open Lean Parsec ByteArray

def parsePartialAssignment : Parser (Bool × (Array (Bool × Nat))) := do
  skipByteChar 'v'
  let idents ← many (attempt wsLit)
  let idents := idents.map (fun i => if i > 0 then (true, i.natAbs) else (false, i.natAbs))
  Parsec.tryCatch
    (skipString " 0")
    (csuccess := fun _ => pure (true, idents))
    (cerror := fun _ => do
      skipByteChar '\n'
      return (false, idents)
    )
where
  @[inline]
  wsLit : Parser Int := do
    skipByteChar ' '
    let lit ← LRAT.Parser.Text.parseLit
    return lit

partial def parseLines : Parser (Array (Bool × Nat)) :=
  go #[]
where
  go (acc : Array (Bool × Nat)) : Parser (Array (Bool × Nat)) := do
    let (terminal?, additionalAssignment) ← parsePartialAssignment
    let acc := acc ++ additionalAssignment
    if terminal? then
      return acc
    else
      go acc

def parseHeader : Parser Unit := do
  skipString "s SATISFIABLE\n"

/--
Parse the witness format of a SAT solver. The rough grammar for this is:
line = "v" (" " lit)* (" " 0)?\n
witness = "s SATISFIABLE\n" line+
-/
def parse : Parser (Array (Bool × Nat)) := do
  parseHeader
  parseLines

end SatWitnessParser

open Lean

partial def runInterruptible (args : IO.Process.SpawnArgs) : CoreM IO.Process.Output := do
  let child ← IO.Process.spawn { args with stdout := .piped, stderr := .piped, stdin := .null }
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  if let some tk := (← read).cancelTk? then
    go child stdout stderr tk
  else
    let stdout ← IO.ofExcept stdout.get
    let stderr ← IO.ofExcept stderr.get
    let exitCode ← child.wait
    return { exitCode := exitCode, stdout := stdout, stderr := stderr }
where
  go {cfg} (child : IO.Process.Child cfg) (stdout stderr : Task (Except IO.Error String))
      (tk : IO.CancelToken) : CoreM IO.Process.Output := do
    withInterruptCheck tk child.kill do
      match ← child.tryWait with
      | some exitCode =>
        let stdout ← IO.ofExcept stdout.get
        let stderr ← IO.ofExcept stderr.get
        return { exitCode := exitCode, stdout := stdout, stderr := stderr }
      | none =>
        IO.sleep 50
        go child stdout stderr tk

  withInterruptCheck {α : Type} (tk : IO.CancelToken) (interrupted : CoreM Unit) (x : CoreM α)
      : CoreM α := do
    if ← tk.isSet then
      interrupted
      throw <| .internal Core.interruptExceptionId
    else
      x

/--
By default, satQuery assumes that the user has cadical (≥ version 1.7.0) installed and their
path set up so that it can be run via the command `cadical` in terminal. If the path to the user's
`cadical` is different, it can be provided in the `solverPath` argument. `satQuery` will call
cadical on the CNF file at `problemPath` and output an LRAT result to `proofOutput`.
-/
def satQuery (solverPath := "cadical") (problemPath : System.FilePath)
    (proofOutput : System.FilePath) (timeout : Nat) (binaryProofs : Bool) : CoreM SolverResult := do
  let cmd := solverPath
  let mut args := #[
    problemPath.toString,
    proofOutput.toString,
    "-t",
    s!"{timeout}",
    "--lrat",
    s!"--binary={binaryProofs}",
    "--quiet",
    "--unsat" -- This sets the magic parameters of cadical to optimize for UNSAT search.
  ]

  let out ← runInterruptible { cmd, args, stdin := .piped, stdout := .piped, stderr := .null }
  if out.exitCode == 255 then
    throwError s!"Failed to execute external prover:\n{out.stderr}"
  else
    let stdout := out.stdout
    if stdout.startsWith "s UNSATISFIABLE" then
      return .unsat
    else if stdout.startsWith "s SATISFIABLE" then
      match SatWitnessParser.parse.run stdout.toUTF8 with
      | .ok assignment =>
        return .sat assignment
      | .error err =>
        throwError s!"Error {err} while parsing:\n{stdout}"
    else if stdout.startsWith "c UNKNOWN" then
      let mut err := "The SAT solver timed out while solving the problem."
      err := err ++ "\nConsider increasing the timeout with `set_option sat.timeout <sec>`"
      throwError err
    else
      throwError s!"The external prover produced unexpected output:\n{stdout}"
