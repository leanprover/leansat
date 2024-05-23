import LeanSAT.Reflect.Tactics.BVDecide
import LeanSAT.Reflect.Tactics.BVCheck
import LeanSAT.Reflect.Tactics.SatTrace
import Lean.Meta.Tactic.TryThis
import Lean.Elab.Tactic.SimpTrace

open Lean Elab Meta Tactic

namespace BVTrace

/--
Suggest a proof script for a `bv_decide` tactic call.
Useful for caching LRAT proofs.
-/
syntax (name := bvTraceSyntax) "bv_decide?" : tactic

@[tactic bvTraceSyntax, inherit_doc bvTraceSyntax]
def evalBvTrace : Tactic := fun stx =>
  match stx with
  | `(tactic| bv_decide?%$tk) => do
    let lratFile : System.FilePath ← SatTrace.getLratFileName
    let cfg ← SatCheck.mkContext lratFile
    let g ← getMainGoal
    let trace ← g.withContext do
      let trace ← g.bvDecide cfg
      replaceMainGoal []
      return trace
    -- TODO: figure out how to make a proper simp only syntax without having an initial simp
    let fake ← `(tactic| simp only [bv_decide, seval] at *)
    let simpStx ← mkSimpCallStx fake trace.simpTrace.usedTheorems
    match trace.lratCert with
    | none =>
      let normalizeStx ← `(tactic| by_contra; $simpStx)
      TryThis.addSuggestion tk normalizeStx (origSpan? := ← getRef)
    | some .. =>
      let bvCheckStx ← `(tactic| by_contra; $simpStx; bv_check $(quote lratFile.toString))
      TryThis.addSuggestion tk bvCheckStx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end BVTrace
