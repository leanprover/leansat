/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.AIG.Basic
import LeanSAT.AIG.Lemmas

/-!
This module contains functions to construct AIG nodes while making use of the sub-circuit cache
if possible. For performance reasons these functions should usually be preferred over the naive
AIG node creation ones.
-/

namespace AIG

variable {α : Type} [BEq α] [Hashable α] [DecidableEq α]

/--
A version of `AIG.mkAtom` that uses the subterm cache in `AIG`. This version is meant for
programmming, for proving purposes use `AIG.mkAtom` and equality theorems to this one.
-/
def mkAtomCached (aig : AIG α) (n : α) : Entrypoint α :=
  let decl := .atom n
  match aig.cache.find? decl with
  | some hit =>
    ⟨aig, hit.idx, hit.hbound⟩
  | none =>
    let g := aig.decls.size
    let decls := aig.decls.push decl
    let cache := aig.cache.insert decl
    have inv := by
      intro i lhs rhs linv rinv h1 h2
      simp only [decls] at *
      simp only [Array.get_push] at h2
      split at h2
      . apply aig.inv <;> assumption
      . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

/--
A version of `AIG.mkConst` that uses the subterm cache in `AIG`. This version is meant for
programmming, for proving purposes use `AIG.mkGate` and equality theorems to this one.
-/
def mkConstCached (aig : AIG α) (val : Bool) : Entrypoint α :=
  let decl := .const val
  match aig.cache.find? decl with
  | some hit =>
    ⟨aig, hit.idx, hit.hbound⟩
  | none =>
    let g := aig.decls.size
    let decls := aig.decls.push decl
    let cache := aig.cache.insert decl
    have inv := by
      intro i lhs rhs linv rinv h1 h2
      simp only [decls] at *
      simp only [Array.get_push] at h2
      split at h2
      . apply aig.inv <;> assumption
      . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

/--
A version of `AIG.mkGate` that uses the subterm cache in `AIG`. This version is meant for
programmming, for proving purposes use `AIG.mkGate` and equality theorems to this one.

Beyond caching this function also implements a subset of the optimizations presented in:
-/
def mkGateCached (aig : AIG α) (input : GateInput aig) : Entrypoint α :=
  let lhs := input.lhs.ref.gate
  let rhs := input.rhs.ref.gate
  let linv := input.lhs.inv
  let rinv := input.rhs.inv
  have := input.lhs.ref.hgate
  have := input.rhs.ref.hgate
  let decl := .gate lhs rhs linv rinv
  match aig.cache.find? decl with
  | some hit =>
    ⟨aig, hit.idx, hit.hbound⟩
  | none =>
    /-
    Here we implement the constant propagating subset of:
    https://fmv.jku.at/papers/BrummayerBiere-MEMICS06.pdf
    TODO: rest of the table
    -/
    match aig.decls[lhs], aig.decls[rhs], linv, rinv with
    -- Boundedness
    | .const true, _, true, _ | .const false, _, false, _
    | _, .const true, _, true | _, .const false, _, false =>
      aig.mkConstCached false
    -- Left Neutrality
    | .const true, _, false, false | .const false, _, true, false =>
      ⟨aig, rhs, (by assumption)⟩
    -- Right Neutrality
    | _, .const true, false, false | _, .const false, false, true =>
      ⟨aig, lhs, (by assumption)⟩
    | _, _, _, _ =>
      let g := aig.decls.size
      let decls := aig.decls.push decl
      let cache := Cache.insert aig.cache decl
      have inv := by
        intro lhs rhs linv rinv i h1 h2
        simp only [decls] at *
        simp only [Array.get_push] at h2
        split at h2
        . apply aig.inv <;> assumption
        . injections; omega
      ⟨{ aig with decls, inv, cache }, g, by simp [g, decls]⟩

end AIG
