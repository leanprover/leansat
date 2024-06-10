import Lean.Meta.AppBuilder
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.FalseOrByContra

import LeanSAT.Reflect.Tactics.Attr
import LeanSAT.Reflect.Tactics.Normalize.Canonicalize
import LeanSAT.Reflect.Tactics.Normalize.Prop
import LeanSAT.Reflect.Tactics.Normalize.Bool
import LeanSAT.Reflect.Tactics.Normalize.BitVec

namespace BVDecide
namespace Normalize

open Lean Elab Meta Tactic

structure Result where
  goal : Option MVarId
  stats : Simp.Stats

def _root_.Lean.MVarId.bvNormalize (g : MVarId) : MetaM Result := do
  withTraceNode `bv (fun _ => return "Normalizing goal") do
    -- Contradiction proof
    let g ← g.falseOrByContra

    -- Normalization by simp
    let bvThms ← bvNormalizeExt.getTheorems
    let bvSimprocs ← bvNormalizeSimprocExt.getSimprocs
    let sevalThms ← getSEvalTheorems
    let sevalSimprocs ← Simp.getSEvalSimprocs

    let simpCtx : Simp.Context := {
      simpTheorems := #[bvThms, sevalThms]
      congrTheorems := (← getSimpCongrTheorems)
    }

    let hyps ← g.getNondepPropHyps
    -- TODO: Think about whether having a discharger might be interesting
    let ⟨result?, stats⟩ ← simpGoal g
      (ctx := simpCtx)
      (simprocs := #[bvSimprocs, sevalSimprocs])
      (fvarIdsToSimp := hyps)
    let some (_, g) := result? | return ⟨none, stats⟩
    return ⟨some g, stats⟩

end Normalize
end BVDecide

syntax (name := bvNormalizeSyntax) "bv_normalize" : tactic

open Lean.Elab.Tactic

elab_rules : tactic
| `(tactic| bv_normalize) => do
  liftMetaFinishingTactic fun g => do
    let _ ← g.bvNormalize
    return ()
