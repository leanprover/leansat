/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Meta.AppBuilder
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.FalseOrByContra

import LeanSAT.Frontend.Attr
import LeanSAT.Frontend.Normalize.Canonicalize
import LeanSAT.Frontend.Normalize.Prop
import LeanSAT.Frontend.Normalize.Bool
import LeanSAT.Frontend.Normalize.BitVec
import LeanSAT.Frontend.Normalize.Equal

/-!
This module contains the implementation of `bv_normalize` which is effectively a custom `bv_normalize`
simp set that is called like this: `simp only [seval, bv_normalize]`. The rules in `bv_normalize`
fulfill two goals:
1. Turn all hypothesis involving `Bool` and `BitVec` into the form `x = true` where `x` only consists
   of a operations on `Bool` and `BitVec`. In particular no `Prop` should be contained. This makes
   the reflection procedure further down the pipeline much easier to implement.
2. Apply simplification rules from the Bitwuzla SMT solver.
-/

namespace BVDecide
namespace Normalize

open Lean
open Lean.Meta

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
