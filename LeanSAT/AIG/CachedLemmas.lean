/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.AIG.Cached

/-!
This module contains the theory of the cached AIG node creation functions.
It is mainly concerned with proving lemmas about the denotational semantics of the gate functions
in different scenarios. In particular reductions to the semantics of the non cached versions.
-/

namespace AIG

variable {α : Type} [BEq α] [Hashable α] [DecidableEq α]

/--
If we find a cached atom declaration in the AIG, denoting it is equivalent to denoting `AIG.mkAtom`.
-/
theorem denote_mkAtom_cached {aig : AIG α} {hit} (h : aig.cache.find? (.atom v) = some hit) :
    ⟦aig, ⟨hit.idx, hit.hbound⟩, assign⟧ = ⟦aig.mkAtom v, assign⟧ := by
  have := hit.hvalid
  simp only [denote_mkAtom]
  unfold denote denote.go
  split <;> simp_all

/--
`mkAtomCached` does not modify the input AIG upon a cache hit.
-/
theorem mkAtomCached_hit_aig (aig : AIG α) {hit} (hcache : aig.cache.find? (.atom var) = some hit) :
    (aig.mkAtomCached var).aig = aig := by
  simp only [mkAtomCached]
  split <;> simp_all

/--
`mkAtomCached` pushes to the input AIG upon a cache miss.
-/
theorem mkAtomCached_miss_aig (aig : AIG α) (hcache : aig.cache.find? (.atom var) = none) :
    (aig.mkAtomCached var).aig.decls = aig.decls.push (.atom var) := by
  simp only [mkAtomCached]
  split <;> simp_all

/--
The AIG produced by `AIG.mkAtomCached` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkAtomCached_decl_eq (aig : AIG α) (var : α) (idx : Nat) {h : idx < aig.decls.size} {hbound} :
    (aig.mkAtomCached var).aig.decls[idx]'hbound = aig.decls[idx] := by
  match hcache:aig.cache.find? (.atom var) with
  | some gate =>
    have := mkAtomCached_hit_aig aig hcache
    simp [this]
  | none =>
    have := mkAtomCached_miss_aig aig hcache
    simp only [this, Array.get_push]
    split
    . rfl
    . contradiction

/--
`AIG.mkAtomCached` never shrinks the underlying AIG.
-/
theorem mkAtomCached_le_size (aig : AIG α) (var : α)
    : aig.decls.size ≤ (aig.mkAtomCached var).aig.decls.size := by
  dsimp [mkAtomCached]
  split
  . simp
  . simp_arith

/--
The central equality theorem between `mkAtomCached` and `mkAtom`.
-/
@[simp]
theorem mkAtomCached_eval_eq_mkAtom_eval {aig : AIG α}
    : ⟦aig.mkAtomCached var, assign⟧ = ⟦aig.mkAtom var, assign⟧ := by
  simp only [mkAtomCached]
  split
  . next heq1 =>
    rw [denote_mkAtom_cached heq1]
  . simp [mkAtom, denote]

/--
If we find a cached const declaration in the AIG, denoting it is equivalent to denoting `AIG.mkConst`.
-/
theorem denote_mkConst_cached {aig : AIG α} {hit} (h : aig.cache.find? (.const b) = some hit) :
    ⟦aig, ⟨hit.idx, hit.hbound⟩, assign⟧ = ⟦aig.mkConst b, assign⟧ := by
  have := hit.hvalid
  simp only [denote_mkConst]
  unfold denote denote.go
  split <;> simp_all

/--
`mkConstCached` does not modify the input AIG upon a cache hit.
-/
theorem mkConstCached_hit_aig (aig : AIG α) {hit} (hcache : aig.cache.find? (.const val) = some hit) :
    (aig.mkConstCached val).aig = aig := by
  simp only [mkConstCached]
  split <;> simp_all

/--
`mkConstCached` pushes to the input AIG upon a cache miss.
-/
theorem mkConstCached_miss_aig (aig : AIG α) (hcache : aig.cache.find? (.const val) = none) :
    (aig.mkConstCached val).aig.decls = aig.decls.push (.const val) := by
  simp only [mkConstCached]
  split <;> simp_all

/--
The AIG produced by `AIG.mkConstCached` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkConstCached_decl_eq (aig : AIG α) (val : Bool) (idx : Nat) {h : idx < aig.decls.size} {hbound} :
    (aig.mkConstCached val).aig.decls[idx]'hbound = aig.decls[idx] := by
  match hcache:aig.cache.find? (.const val) with
  | some gate =>
    have := mkConstCached_hit_aig aig hcache
    simp [this]
  | none =>
    have := mkConstCached_miss_aig aig hcache
    simp only [this, Array.get_push]
    split
    . rfl
    . contradiction

/--
`AIG.mkConstCached` never shrinks the underlying AIG.
-/
theorem mkConstCached_le_size (aig : AIG α) (val : Bool)
    : aig.decls.size ≤ (aig.mkConstCached val).aig.decls.size := by
  dsimp [mkConstCached]
  split
  . simp
  . simp_arith

/--
We can show that something is < the output AIG of `mkConstCached` by showing that it is < the input AIG.
-/
theorem lt_mkConstCached_size_of_lt_aig_size (aig : AIG α) (val : Bool) (h : x < aig.decls.size) :
    x < (aig.mkConstCached val).aig.decls.size := by
  have := mkConstCached_le_size aig val
  omega

/--
We can show that something is ≤ the output AIG of `mkConstCached` by showing that it is ≤ the input AIG.
-/
theorem le_mkConstCached_size_of_le_aig_size (aig : AIG α) (val : Bool) (h : x ≤ aig.decls.size) :
    x ≤ (aig.mkConstCached val).aig.decls.size := by
  have := mkConstCached_le_size aig val
  omega

/--
Reusing an `AIG.Entrypoint` to build an additional constant will never invalidate the entry node of
the original entrypoint.
-/
theorem lt_mkConstCached_size (entry : Entrypoint α) : entry.start < (entry.aig.mkConstCached val).aig.decls.size := by
  have h1 := entry.inv
  have h2 : entry.aig.decls.size ≤ (entry.aig.mkConstCached val).aig.decls.size :=
    AIG.mkConstCached_le_size _ _
  omega

theorem mkConstCached_IsPrefix_aig {aig : AIG α} : IsPrefix aig.decls (mkConstCached val aig).aig.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkConstCached_decl_eq
  . apply mkConstCached_le_size

@[simp]
theorem denote_mkConstCached_entry (entry : Entrypoint α) {h} :
    ⟦(entry.aig.mkConstCached val).aig, ⟨entry.start, h⟩, assign⟧
      =
    ⟦entry, assign⟧ := by
  apply denote.eq_of_aig_eq
  apply mkConstCached_IsPrefix_aig

theorem denote_mkConstCached_mem_prefix {aig : AIG α} (h) :
    ⟦(aig.mkConstCached val).aig, ⟨start, by apply lt_mkConstCached_size_of_lt_aig_size; assumption⟩, assign⟧
      =
    ⟦aig, ⟨start, h⟩, assign⟧ := by
  rw [denote_mkConstCached_entry ⟨aig, start, h⟩]

/--
The central equality theorem between `mkConstCached` and `mkConst`.
-/
@[simp]
theorem mkConstCached_eval_eq_mkConst_eval {aig : AIG α}
    : ⟦aig.mkConstCached val, assign⟧ = ⟦aig.mkConst val, assign⟧ := by
  simp only [mkConstCached]
  split
  . next heq1 =>
    rw [denote_mkConst_cached heq1]
  . simp [mkConst, denote]

/--
If we find a cached gate declaration in the AIG, denoting it is equivalent to denoting `AIG.mkGate`.
-/
theorem denote_mkGate_cached {aig : AIG α} {hl} {hr} {hit}
    (h : aig.cache.find? (.gate lhs rhs lpol rpol) = some hit) :
    ⟦⟨aig, hit.idx, hit.hbound⟩, assign⟧
      =
    ⟦aig.mkGate lhs rhs lpol rpol hl hr, assign⟧ := by
  have := hit.hvalid
  simp only [denote_mkGate]
  conv =>
    lhs
    unfold denote denote.go
  split <;> simp_all[denote]

/--
`AIG.mkGateCached` never shrinks the underlying AIG.
-/
theorem mkGateCached_le_size (aig : AIG α) (lhs rhs : Nat) (linv rinv : Bool) hl hr
    : aig.decls.size ≤ (aig.mkGateCached lhs rhs linv rinv hl hr).aig.decls.size := by
  dsimp [mkGateCached]
  split
  . simp
  . split <;> simp_arith [mkConstCached_le_size]

/--
We can show that something is < the output AIG of `mkGateCached` by showing that it is < the input AIG.
-/
theorem lt_mkGateCached_size_of_lt_aig_size (aig : AIG α) (lhs rhs : Nat) (linv rinv : Bool) (hl) (hr) (h : x < aig.decls.size)
    : x < (aig.mkGateCached lhs rhs linv rinv hl hr).aig.decls.size := by
  have := mkGateCached_le_size aig lhs rhs linv rinv hl hr
  omega

/--
We can show that something is ≤ the output AIG of `mkGateCached` by showing that it is ≤ the input AIG.
-/
theorem le_mkGateCached_size_of_le_aig_size (aig : AIG α) (lhs rhs : Nat) (linv rinv : Bool) (hl) (hr) (h : x ≤ aig.decls.size)
    : x ≤ (aig.mkGateCached lhs rhs linv rinv hl hr).aig.decls.size := by
  have := mkGateCached_le_size aig lhs rhs linv rinv hl hr
  omega

/--
Reusing an `AIG.Entrypoint` to build an additional gate will never invalidate the entry node of
the original entrypoint.
-/
theorem lt_mkGateCached_size (entry : Entrypoint α) (lhs rhs : Nat) (linv rinv : Bool) hl hr
    : entry.start < (entry.aig.mkGateCached lhs rhs linv rinv hl hr).aig.decls.size := by
  apply lt_mkGateCached_size_of_lt_aig_size
  exact entry.inv

/--
`mkGateCached` does not modify the input AIG upon a cache hit.
-/
theorem mkGateCached_hit_aig (aig : AIG α) {hit} (hcache : aig.cache.find? (.gate lhs rhs linv rinv) = some hit) (hl) (hr) :
    (aig.mkGateCached lhs rhs linv rinv hl hr).aig = aig := by
  simp only [mkGateCached]
  split <;> simp_all

theorem mkGateCached_decl_eq? (aig : AIG α) (lhs rhs : Nat) (linv rinv : Bool)
    (h : idx < aig.decls.size) {hl} {hr} (hbound : idx < (aig.mkGateCached lhs rhs linv rinv hl hr).aig.decls.size) :
    (aig.mkGateCached lhs rhs linv rinv hl hr).aig.decls[idx]? = aig.decls[idx]? := by
  unfold mkGateCached
  dsimp
  split
  . next hcache =>
    simp [mkGateCached_hit_aig aig hcache hl hr]
  . next hit hcache =>
    split
    . rw [Array.getElem?_lt, Array.getElem?_lt]
      rw [mkConstCached_decl_eq]
      . apply lt_mkConstCached_size_of_lt_aig_size
        assumption
      . assumption
    . rw [Array.getElem?_lt, Array.getElem?_lt]
      rw [mkConstCached_decl_eq]
      . apply lt_mkConstCached_size_of_lt_aig_size
        assumption
      . assumption
    . rw [Array.getElem?_lt, Array.getElem?_lt]
      rw [mkConstCached_decl_eq]
      . apply lt_mkConstCached_size_of_lt_aig_size
        assumption
      . assumption
    . rw [Array.getElem?_lt, Array.getElem?_lt]
      rw [mkConstCached_decl_eq]
      . apply lt_mkConstCached_size_of_lt_aig_size
        assumption
      . assumption
    . simp only [Array.getElem?_lt]
    . simp only [Array.getElem?_lt]
    . simp only [Array.getElem?_lt]
    . simp only [Array.getElem?_lt]
    . dsimp
      rw [Array.getElem?_lt, Array.getElem?_lt]
      apply congrArg
      rw [Array.get_push]
      split
      . simp
      . contradiction
      . simp only [Array.size_push]
        omega
      . assumption

/--
The AIG produced by `AIG.mkGateCached` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkGateCached_decl_eq idx (aig : AIG α) (lhs rhs : Nat) (linv rinv : Bool)
    {h : idx < aig.decls.size} {hl} {hr} {hbound} :
    (aig.mkGateCached lhs rhs linv rinv hl hr).aig.decls[idx]'hbound = aig.decls[idx]'h := by
  have := mkGateCached_decl_eq? aig lhs rhs linv rinv h hbound
  rw [Array.getElem?_lt, Array.getElem?_lt] at this
  injection this

/--
The input AIG to an `AIG.mkGateCached` is a prefix to the output AIG.
-/
theorem mkGateCached_IsPrefix_aig {aig : AIG α} {hl} {hr} :
    IsPrefix aig.decls (aig.mkGateCached lhs rhs lpol rpol hl hr).aig.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkGateCached_decl_eq
  . apply mkGateCached_le_size

@[simp]
theorem denote_mkGateCached_entry (entry : Entrypoint α) {hlbound} {hrbound} {h} :
    ⟦(entry.aig.mkGateCached lhs rhs lpol rpol hlbound hrbound).aig, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_aig_eq
  apply mkGateCached_IsPrefix_aig

theorem denote_mkGateCached_mem_prefix {aig : AIG α} {hlbound} {hrbound} (h) :
    ⟦(aig.mkGateCached lhs rhs lpol rpol hlbound hrbound).aig, ⟨start, (by apply lt_mkGateCached_size_of_lt_aig_size; assumption)⟩, assign ⟧
      =
    ⟦aig, ⟨start, h⟩, assign⟧ :=  by
  rw [denote_mkGateCached_entry ⟨aig, start, h⟩]

/--
The central equality theorem between `mkGateCached` and `mkGate`.
-/
@[simp]
theorem mkGateCached_eval_eq_mkGate_eval {aig : AIG α} {hl} {hr} :
    ⟦aig.mkGateCached lhs rhs linv rinv hl hr, assign⟧ = ⟦aig.mkGate lhs rhs linv rinv hl hr, assign⟧ := by
  simp only [mkGateCached]
  split
  . next heq1 =>
    rw [denote_mkGate_cached heq1]
  . split
    . next heq _ _ =>
      simp [denote_idx_const heq]
    . next heq _ _ =>
      simp [denote_idx_const heq]
    . next heq _ _ _ _ =>
      simp [denote_idx_const heq]
    . next heq _ _ _ _ =>
      simp [denote_idx_const heq]
    . next heq _ _ _ =>
      simp [denote_idx_const heq]
    . next heq _ _ _ =>
      simp [denote_idx_const heq]
    . next heq _ _ _ _ =>
      simp [denote_idx_const heq]
    . next heq _ _ _ =>
      simp [denote_idx_const heq]
    . simp [mkGate, denote]
end AIG
