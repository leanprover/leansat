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
  let ⟨decls, cache, inv⟩ := aig
  let decl := .atom n
  match cache.find? decl with
  | some hit =>
    ⟨⟨decls, cache, inv⟩ , hit.idx, hit.hbound⟩
  | none =>
    let g := decls.size
    let cache := cache.insert decls decl
    let decls := decls.push decl
    have inv := by
      intro i lhs rhs linv rinv h1 h2
      simp only [decls] at *
      simp only [Array.get_push] at h2
      split at h2
      . apply inv <;> assumption
      . contradiction
  ⟨⟨decls, cache, inv⟩, ⟨g, by simp [g, decls]⟩⟩

/--
A version of `AIG.mkConst` that uses the subterm cache in `AIG`. This version is meant for
programmming, for proving purposes use `AIG.mkGate` and equality theorems to this one.
-/
def mkConstCached (aig : AIG α) (val : Bool) : Entrypoint α :=
  let ⟨decls, cache, inv⟩ := aig
  let decl := .const val
  match cache.find? decl with
  | some hit =>
    ⟨⟨decls, cache, inv⟩, hit.idx, hit.hbound⟩
  | none =>
    let g := decls.size
    let cache := cache.insert decls decl
    let decls := decls.push decl
    have inv := by
      intro i lhs rhs linv rinv h1 h2
      simp only [decls] at *
      simp only [Array.get_push] at h2
      split at h2
      . apply inv <;> assumption
      . contradiction
  ⟨⟨decls, cache, inv⟩, ⟨g, by simp [g, decls]⟩⟩

/--
A version of `AIG.mkGate` that uses the subterm cache in `AIG`. This version is meant for
programmming, for proving purposes use `AIG.mkGate` and equality theorems to this one.

Beyond caching this function also implements a subset of the optimizations presented in:
-/
def mkGateCached (aig : AIG α) (input : GateInput aig) : Entrypoint α :=
  let ⟨decls, cache, inv⟩ := aig
  let lhs := input.lhs.ref.gate
  let rhs := input.rhs.ref.gate
  let linv := input.lhs.inv
  let rinv := input.rhs.inv
  have lhgate := input.lhs.ref.hgate
  have rhgate := input.rhs.ref.hgate
  let decl := .gate lhs rhs linv rinv
  match cache.find? decl with
  | some hit =>
    ⟨⟨decls, cache, inv⟩, ⟨hit.idx, hit.hbound⟩⟩
  | none =>
    /-
    We looked into implementing AIG optimization according to:
    https://fmv.jku.at/papers/BrummayerBiere-MEMICS06.pdf
    However the constant folding subset of this seemed to *decrease* SAT solver performance noticeably.
    We thus decided to just do the naive approach.
    -/
    let g := decls.size
    let cache := cache.insert decls decl
    let decls := decls.push decl
    have inv := by
      intro lhs rhs linv rinv i h1 h2
      simp only [decls] at *
      simp only [Array.get_push] at h2
      split at h2
      . apply inv <;> assumption
      . injections; omega
    ⟨⟨decls, cache, inv⟩, ⟨g, by simp [g, decls]⟩⟩

end AIG
