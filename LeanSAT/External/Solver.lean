/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
open IO.Process

/-- By default, satQuery assumes that the user has cadical (≥ version 1.7.0) installed and their path set up so that it
    can be run via the command `cadical` in terminal. If the path to the user's `cadical` is different, it can be provided
    in the `solverPath` argument. `satQuery` will call cadical on the CNF file at `problemPath` and output an LRAT result
    to `proofOutput` -/
def satQuery (solverPath := "cadical") (problemPath : System.FilePath) (proofOutput : System.FilePath) : IO Unit := do
  let cmd := solverPath
  let args := #[problemPath.toString, proofOutput.toString, "--lrat", "--no-binary", "--quiet"]
  let out ← output ⟨⟨Stdio.inherit, Stdio.inherit, Stdio.inherit⟩, cmd, args, none, #[], false⟩
  if out.exitCode == 255 then
    throw <| IO.userError s!"Failed to execute external prover:\n{out.stderr}"
  else
    if out.stdout.startsWith "s UNSATISFIABLE" then
      return ()
    else if out.stdout.startsWith "s SATISFIABLE" then
      -- TODO: present the counter example
      throw <| IO.userError "The external prover found a counter example"
    else
      throw <| IO.userError s!"The external prover produced unexpected output:\n{out.stdout}"
