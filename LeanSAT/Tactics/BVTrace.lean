/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Tactics.BVDecide
import LeanSAT.Tactics.BVCheck
import LeanSAT.LRAT.Trim
import Lean.Meta.Tactic.TryThis

open Lean Elab Meta Tactic

namespace BVTrace

-- TODO: think of a more maintainable file pattern for this stuff.
/--
Produce a file with the pattern:
LeanFileName-DeclName-Line-Col.lrat
-/
def getLratFileName : TermElabM System.FilePath := do
  let some baseName := System.FilePath.mk (← getFileName) |>.fileName | throwError "could not find file name"
  let some declName ← Term.getDeclName? | throwError "could not find declaration name"
  let pos := (← getFileMap).toPosition (← getRefPos)
  return s!"{baseName}-{declName}-{pos.line}-{pos.column}.lrat"

/--
Suggest a proof script for a `bv_decide` tactic call.
Useful for caching LRAT proofs.
-/
syntax (name := bvTraceSyntax) "bv_decide?" : tactic

@[tactic bvTraceSyntax, inherit_doc bvTraceSyntax]
def evalBvTrace : Tactic := fun stx =>
  match stx with
  | `(tactic| bv_decide?%$tk) => do
    let lratFile : System.FilePath ← getLratFileName
    let cfg := { (← BVCheck.mkContext lratFile) with trimProofs := false }
    let g ← getMainGoal
    let trace ← g.withContext do
      g.bvDecide cfg
    /-
    Ideally trace.lratCert would be the `ByteArray` version of the proof already and we just write
    it. This isn't yet possible so instead we do the following:
    1. Produce the proof in the tactic.
    2. Skip trimming it in the tactic.
    3. Run trimming on the LRAT file that was produced by the SAT solver directly, emitting the
       correct binary format according to `sat.binaryProofs`.
    TODO: Fix this hack:
    1. Introduce `ByteArray` literals to the kernel.
    2. Just return the fully trimmed proof in the format desired by the configuration from `bvDecide`.
    3. Write it to the file driectly.
    -/
    match trace.lratCert with
    | none =>
      let normalizeStx ← `(tactic| bv_normalize)
      TryThis.addSuggestion tk normalizeStx (origSpan? := ← getRef)
    | some .. =>
      if sat.trimProofs.get (← getOptions) then
        let lratPath := (← BVCheck.getSrcDir) / lratFile
        LRAT.trimFile lratPath lratPath cfg.binaryProofs
      let bvCheckStx ← `(tactic| bv_check $(quote lratFile.toString))
      TryThis.addSuggestion tk bvCheckStx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end BVTrace
