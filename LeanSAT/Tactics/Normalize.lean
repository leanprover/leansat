/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Meta.AppBuilder
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.FalseOrByContra

import LeanSAT.Tactics.Attr
import LeanSAT.Tactics.Normalize.Canonicalize
import LeanSAT.Tactics.Normalize.Prop
import LeanSAT.Tactics.Normalize.Bool
import LeanSAT.Tactics.Normalize.BitVec
import LeanSAT.Tactics.Normalize.Equal

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
