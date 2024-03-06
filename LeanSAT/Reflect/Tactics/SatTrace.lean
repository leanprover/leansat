import LeanSAT.Reflect.Tactics.SatDecide
import LeanSAT.Reflect.Tactics.SatCheck
import Lean.Meta.Tactic.TryThis

open Lean Elab Meta Tactic

namespace SatTrace

/--
Suggest a `sat_check` invocation for a `sat_decide` tactic call.
Useful for caching LRAT proofs.
-/
syntax (name := satTraceSyntax) "sat_decide?" : tactic

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

@[tactic satTraceSyntax, inherit_doc satTraceSyntax]
def evalSatTraceTactic : Tactic := fun stx =>
  match stx with
  | `(tactic| sat_decide?%$tk) => do
    let lratFile : System.FilePath ← getLratFileName
    let cfg ← SatCheck.mkContext lratFile
    (← getMainGoal).withContext do
      liftMetaFinishingTactic fun g => g.satDecide cfg
    let stx ← `(tactic| sat_check $(quote lratFile.toString))
    TryThis.addSuggestion tk stx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end SatTrace
