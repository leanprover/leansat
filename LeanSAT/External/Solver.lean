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
def satQuery (solverPath := "cadical") (problemPath : String) (proofOutput := "./temp.lrat") : IO Output := do
  let cmd := solverPath
  let args := #[problemPath, proofOutput, "--lrat", "--no-binary", "--quiet"]
  output ⟨⟨Stdio.inherit, Stdio.inherit, Stdio.inherit⟩, cmd, args, none, #[], false⟩
