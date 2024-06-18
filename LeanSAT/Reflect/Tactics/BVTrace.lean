import LeanSAT.Reflect.Tactics.BVDecide
import LeanSAT.Reflect.Tactics.BVCheck
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
    let cfg ← BVCheck.mkContext lratFile
    let g ← getMainGoal
    let trace ← g.withContext do
      g.bvDecide cfg
    match trace.lratCert with
    | none =>
      let normalizeStx ← `(tactic| bv_normalize)
      TryThis.addSuggestion tk normalizeStx (origSpan? := ← getRef)
    | some .. =>
      -- TODO: add an option?
      let lratPath := (← BVCheck.getSrcDir) / lratFile
      LRAT.trim lratPath lratPath
      let bvCheckStx ← `(tactic| bv_check $(quote lratFile.toString))
      TryThis.addSuggestion tk bvCheckStx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end BVTrace
