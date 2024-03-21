/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.Tactics.Reflect
import LeanSAT.AIG.Basic

/-!
This module provides a basic theory around the naive AIG node creation functions. It is mostly
fundamental work for the cached versions later on.
-/

namespace AIG

variable {α : Type} [BEq α] [Hashable α] [DecidableEq α]

/--
`decls` is a prefix of `decls2`
-/
structure IsPrefix (decls1 decls2 : Array (Decl α)) : Prop where
  /--
  The prefix may never be longer than the other array.
  -/
  size_le : decls1.size ≤ decls2.size
  /--
  The prefix and the other array must agree on all elements up until the bound of the prefix
  -/
  idx_eq : ∀ idx (h : idx < decls1.size), decls2[idx]'(by omega) = decls1[idx]'h

/--
The cannonical way to prove that an array is a prefix of another array.
-/
theorem IsPrefix.of {decls1 decls2 : Array (Decl α)}
    (size_le : decls1.size ≤ decls2.size)
    (idx_eq : ∀ idx (h : idx < decls1.size), decls2[idx]'(by omega) = decls1[idx]'h)
    : IsPrefix decls1 decls2 := ⟨size_le, idx_eq⟩

/--
If `decls1` is a prefix of `decls2` and we start evaluating `decls2` at an
index in bounds of `decls1` we can evluate at `decls1`.
-/
theorem denote.go_eq_of_aig_eq (decls1 decls2 : Array (Decl α)) (start : Nat) {hdag1} {hdag2}
    {hbounds1} {hbounds2} (hprefix : IsPrefix decls1 decls2) :
    denote.go start decls2 assign hbounds2 hdag2
      =
    denote.go start decls1 assign hbounds1 hdag1 := by
  unfold denote.go
  have hidx1 := hprefix.idx_eq start hbounds1
  split
  . next heq =>
    rw [hidx1] at heq
    split <;> simp_all
  . next heq =>
    rw [hidx1] at heq
    split <;> simp_all
  . next lhs rhs linv rinv heq =>
    rw [hidx1] at heq
    have foo := hdag1 start lhs rhs linv rinv hbounds1 heq
    have hidx2 := hprefix.idx_eq lhs (by omega)
    have hidx3 := hprefix.idx_eq rhs (by omega)
    split
    . simp_all
    . simp_all
    . simp_all
      apply ReflectSat.EvalAtAtoms.and_congr
      all_goals
        apply ReflectSat.EvalAtAtoms.xor_congr
        . apply denote.go_eq_of_aig_eq
          assumption
        . rfl
termination_by sizeOf start

/--
Running `AIG.denote.go` on a node that is within bounds of `decls` is equivalent to running it a bigger `decls` array.
-/
theorem denote.go_lt_push (x : Nat) (decls : Array (Decl α)) {h1} {h2} {h3} :
    (denote.go x (decls.push decl) assign (by simp; omega) h3) = (denote.go x decls assign h1 h2)  := by
  apply denote.go_eq_of_aig_eq
  apply IsPrefix.of
  . intro idx h
    simp only [Array.get_push]
    split
    . rfl
    . contradiction
  . simp_arith

@[inherit_doc denote.go_eq_of_aig_eq ]
theorem denote.eq_of_aig_eq (entry : Entrypoint α) (newAIG : AIG α) (hprefix : IsPrefix entry.aig.decls newAIG.decls) :
    ⟦newAIG, ⟨entry.start, (by have := entry.inv; have := hprefix.size_le; omega)⟩, assign⟧
      =
    ⟦entry, assign⟧
    := by
  unfold denote
  apply denote.go_eq_of_aig_eq
  assumption

@[simp]
theorem denote_projected_entry {entry : Entrypoint α} :
    ⟦entry.aig, ⟨entry.start, entry.inv⟩, assign⟧ = ⟦entry, assign⟧ := by
  cases entry; simp

/--
`AIG.mkGate` never shrinks the underlying AIG.
-/
theorem mkGate_le_size (aig : AIG α) (lhs rhs : Nat) (linv rinv : Bool) (hl) (hr)
    : aig.decls.size ≤ (aig.mkGate lhs rhs linv rinv hl hr).aig.decls.size := by
  simp_arith [mkGate]

/--
The AIG produced by `AIG.mkGate` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkGate_decl_eq idx (aig : AIG α) (lhs rhs : Nat) (linv rinv : Bool) {h : idx < aig.decls.size} {hl} {hr} :
    have := mkGate_le_size aig lhs rhs linv rinv hl hr
    (aig.mkGate lhs rhs linv rinv hl hr).aig.decls[idx]'(by omega) = aig.decls[idx] := by
  simp only [mkGate, Array.get_push]
  split
  . rfl
  . contradiction

/--
The input AIG to an `mkGate` is a prefix to the output AIG.
-/
theorem mkGate_IsPrefix_aig (aig : AIG α) (lhs rhs : Nat) (linv rinv : Bool) {hl} {hr} :
    IsPrefix aig.decls (aig.mkGate lhs rhs linv rinv hl hr).aig.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkGate_decl_eq
  . apply mkGate_le_size

@[simp]
theorem denote_mkGate {aig : AIG α} {hl} {hr} :
    ⟦aig.mkGate lhs rhs linv rinv hl hr, assign⟧
      =
    ((xor ⟦aig, ⟨lhs, hl⟩, assign⟧ linv) && (xor ⟦aig, ⟨rhs, hr⟩, assign⟧ rinv)) := by
  conv =>
    lhs
    unfold denote denote.go
  split
  . next heq =>
    rw [mkGate, Array.get_push_size] at heq
    contradiction
  . next heq =>
    rw [mkGate, Array.get_push_size] at heq
    contradiction
  . next heq =>
    rw [mkGate, Array.get_push_size] at heq
    injection heq with heq1 heq2 heq3 heq4
    simp
    apply ReflectSat.EvalAtAtoms.and_congr
    all_goals
      apply ReflectSat.EvalAtAtoms.xor_congr
      . unfold denote
        simp only [heq1, heq2]
        apply denote.go_eq_of_aig_eq
        apply mkGate_IsPrefix_aig
      . simp only [heq3, heq4]

/--
We can show that something is < the output AIG of `mkGate` by showing that it is < the input AIG.
-/
theorem lt_mkGate_size_of_lt_aig_size (aig : AIG α) (lhs rhs : Nat) (linv rinv : Bool) (hl) (hr) (h : x < aig.decls.size)
    : x < (aig.mkGate lhs rhs linv rinv hl hr).aig.decls.size := by
  have := mkGate_le_size aig lhs rhs linv rinv hl hr
  omega

/--
Reusing an `AIG.Entrypoint` to build an additional gate will never invalidate the entry node of
the original entrypoint.
-/
theorem lt_mkGate_size (entry : Entrypoint α) (lhs rhs : Nat) (linv rinv : Bool) (hl) (hr)
    : entry.start < (entry.aig.mkGate lhs rhs linv rinv hl hr).aig.decls.size := by
  apply lt_mkGate_size_of_lt_aig_size
  exact entry.inv

/--
We can show that something is ≤ the output AIG of `mkGate` by showing that it is ≤ the input AIG.
-/
theorem le_mkGate_size_of_le_aig_size (aig : AIG α) (lhs rhs : Nat) (linv rinv : Bool) (hl) (hr) (h : x ≤ aig.decls.size)
    : x ≤ (aig.mkGate lhs rhs linv rinv hl hr).aig.decls.size := by
  have := mkGate_le_size aig lhs rhs linv rinv hl hr
  omega

@[simp]
theorem denote_mkGate_entry (entry : Entrypoint α) {hlbound} {hrbound} {h} :
    ⟦(entry.aig.mkGate lhs rhs lpol rpol hlbound hrbound).aig, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_aig_eq
  apply mkGate_IsPrefix_aig

@[simp]
theorem denote_mkGate_lhs (entry : Entrypoint α) {hlbound} {hrbound} {h} :
    ⟦(entry.aig.mkGate lhs rhs lpol rpol hlbound hrbound).aig, ⟨lhs, h⟩, assign⟧
      =
    ⟦entry.aig, ⟨lhs, hlbound⟩, assign⟧ :=  by
  apply denote.go_eq_of_aig_eq
  apply mkGate_IsPrefix_aig
  . assumption
  . assumption

@[simp]
theorem denote_mkGate_rhs (entry : Entrypoint α) {hlbound} {hrbound} {h} :
    ⟦(entry.aig.mkGate lhs rhs lpol rpol hlbound hrbound).aig, ⟨rhs, h⟩, assign⟧
      =
    ⟦entry.aig, ⟨rhs, hrbound⟩, assign⟧ :=  by
  apply denote.go_eq_of_aig_eq
  apply mkGate_IsPrefix_aig
  . assumption
  . assumption

/--
`AIG.mkAtom` never shrinks the underlying AIG.
-/
theorem mkAtom_le_size (aig : AIG α) (var : α) : aig.decls.size ≤ (aig.mkAtom var).aig.decls.size := by
  simp_arith [mkAtom]

/--
The AIG produced by `AIG.mkAtom` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkAtom_decl_eq (aig : AIG α) (var : α) (idx : Nat) {h : idx < aig.decls.size} {hbound} :
    (aig.mkAtom var).aig.decls[idx]'hbound = aig.decls[idx] := by
  simp only [mkAtom, Array.get_push]
  split
  . rfl
  . contradiction

/--
The input AIG to an `mkAtom` is a prefix to the output AIG.
-/
theorem mkAtom_IsPrefix_aig (aig : AIG α) (var : α) :
    IsPrefix aig.decls (aig.mkAtom var).aig.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkAtom_decl_eq
  . apply mkAtom_le_size

@[simp]
theorem denote_mkAtom {aig : AIG α} :
    ⟦(aig.mkAtom var), assign⟧ = assign var := by
  unfold denote denote.go
  split
  . next heq =>
    rw [mkAtom, Array.get_push_size] at heq
    contradiction
  . next heq =>
    rw [mkAtom, Array.get_push_size] at heq
    injection heq with heq
    rw [heq]
  . next heq =>
    rw [mkAtom, Array.get_push_size] at heq
    contradiction

@[simp]
theorem denote_mkAtom_lt (entry : Entrypoint α) {h} :
    ⟦(entry.aig.mkAtom var).aig, ⟨entry.start, h⟩, assign⟧
      =
    ⟦entry, assign⟧ := by
  apply denote.eq_of_aig_eq
  apply mkAtom_IsPrefix_aig

/--
`AIG.mkConst` never shrinks the underlying AIG.
-/
theorem mkConst_le_size (aig : AIG α) (val : Bool)
    : aig.decls.size ≤ (aig.mkConst val).aig.decls.size := by
  simp_arith [mkConst]

/--
The AIG produced by `AIG.mkConst` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkConst_decl_eq (aig : AIG α) (val : Bool) (idx : Nat) {h : idx < aig.decls.size} :
    have := mkConst_le_size aig val
    (aig.mkConst val).aig.decls[idx]'(by omega) = aig.decls[idx] := by
  simp only [mkConst, Array.get_push]
  split
  . rfl
  . contradiction

/--
The input AIG to an `mkConst` is a prefix to the output AIG.
-/
theorem mkConst_IsPrefix_aig (aig : AIG α) (const : Bool) :
    IsPrefix aig.decls (aig.mkConst const).aig.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkConst_decl_eq
  . apply mkConst_le_size

@[simp]
theorem denote_mkConst {aig : AIG α} : ⟦(aig.mkConst val), assign⟧ = val := by
  unfold denote denote.go
  split
  . next heq =>
    rw [mkConst, Array.get_push_size] at heq
    injection heq with heq
    rw [heq]
  . next heq =>
    rw [mkConst, Array.get_push_size] at heq
    contradiction
  . next heq =>
    rw [mkConst, Array.get_push_size] at heq
    contradiction

@[simp]
theorem denote_mkConst_entry (entry : Entrypoint α) {h} :
    ⟦(entry.aig.mkConst val).aig, ⟨entry.start, h⟩, assign⟧
      =
    ⟦entry, assign⟧ := by
  apply denote.eq_of_aig_eq
  apply mkConst_IsPrefix_aig

/--
We can show that something is < the output AIG of `mkConst` by showing that it is < the input AIG.
-/
theorem lt_mkConst_size_of_lt_aig_size (aig : AIG α) (val : Bool) (h : x < aig.decls.size) : x < (aig.mkConst val).aig.decls.size := by
  have := mkConst_le_size aig val
  omega

/--
Reusing an `AIG.Entrypoint` to build an additional constant will never invalidate the entry node of
the original entrypoint.
-/
theorem lt_mkConst_size (entry : Entrypoint α) (val : Bool) : entry.start < (entry.aig.mkConst val).aig.decls.size := by
  apply lt_mkConst_size_of_lt_aig_size
  exact entry.inv

/--
We can show that something is ≤ the output AIG of `mkConst` by showing that it is ≤ the input AIG.
-/
theorem le_mkConst_size_of_le_aig_size (aig : AIG α) (val : Bool) (h : x ≤ aig.decls.size) : x ≤ (aig.mkConst val).aig.decls.size := by
  have := mkConst_le_size aig val
  omega

/--
If an index contains a `Decl.const` we know how to denote it.
-/
theorem denote_idx_const {aig : AIG α} {hstart} (h : aig.decls[start]'hstart = .const b) :
    ⟦aig, ⟨start, hstart⟩, assign⟧ = b := by
  unfold denote denote.go
  split <;> simp_all

/--
If an index contains a `Decl.atom` we know how to denote it.
-/
theorem denote_idx_atom {aig : AIG α} {hstart} (h : aig.decls[start] = .atom a) :
    ⟦aig, ⟨start, hstart⟩, assign⟧ = assign a := by
  unfold denote denote.go
  split <;> simp_all

/--
If an index contains a `Decl.gate` we know how to denote it.
-/
theorem denote_idx_gate {aig : AIG α} {hstart} (h : aig.decls[start] = .gate lhs rhs linv rinv) :
    ⟦aig, ⟨start, hstart⟩, assign⟧
      =
    (
      (xor ⟦aig, ⟨lhs, by have := aig.inv start lhs rhs linv rinv hstart h; omega⟩, assign⟧ linv)
        &&
      (xor ⟦aig, ⟨rhs, by have := aig.inv start lhs rhs linv rinv hstart h; omega⟩, assign⟧ rinv)
    ) := by
  unfold denote
  conv =>
    lhs
    unfold denote.go
  split
  . simp_all
  . simp_all
  . next heq =>
    rw [h] at heq
    simp_all

theorem idx_trichotomy (aig : AIG α) (hstart : start < aig.decls.size) {prop : Prop}
    (hconst : ∀ b, aig.decls[start]'hstart = .const b → prop)
    (hatom : ∀ a, aig.decls[start]'hstart = .atom a → prop)
    (hgate : ∀ lhs rhs linv rinv, aig.decls[start]'hstart = .gate lhs rhs linv rinv → prop)
    : prop := by
  match h:aig.decls[start]'hstart with
  | .const b => apply hconst; assumption
  | .atom a => apply hatom; assumption
  | .gate lhs rhs linv rinv => apply hgate; assumption

theorem denote_idx_trichotomy {aig : AIG α} {hstart : start < aig.decls.size}
    (hconst : ∀ b, aig.decls[start]'hstart = .const b → ⟦aig, ⟨start, hstart⟩, assign⟧ = res)
    (hatom : ∀ a, aig.decls[start]'hstart = .atom a → ⟦aig, ⟨start, hstart⟩, assign⟧ = res)
    (hgate : ∀ lhs rhs linv rinv, aig.decls[start]'hstart = .gate lhs rhs linv rinv → ⟦aig, ⟨start, hstart⟩, assign⟧ = res)
    : ⟦aig, ⟨start, hstart⟩, assign⟧ = res := by
  apply idx_trichotomy aig hstart
  . exact hconst
  . exact hatom
  . exact hgate

theorem mem_def {aig : AIG α} {a : α} : (a ∈ aig) = ((.atom a) ∈ aig.decls) := by
  simp [Membership.mem, mem]

theorem denote_congr (assign1 assign2 : α → Bool) (aig : AIG α) (idx : Nat)
    (hidx : idx < aig.decls.size) (h : ∀ a, a ∈ aig → assign1 a = assign2 a)
    : ⟦aig, ⟨idx, hidx⟩, assign1⟧ = ⟦aig, ⟨idx, hidx⟩, assign2⟧ := by
  apply denote_idx_trichotomy
  . intro b heq
    simp [denote_idx_const heq]
  . intro a heq
    simp only [denote_idx_atom heq]
    apply h
    rw [mem_def]
    rw [← heq]
    -- TODO: this should be in the array API
    rw [Array.mem_def]
    apply Array.getElem_mem_data
  . intro lhs rhs linv rinv heq
    simp [denote_idx_gate heq]
    have := aig.inv idx lhs rhs linv rinv hidx heq
    rw [denote_congr assign1 assign2 aig lhs (by omega) h]
    rw [denote_congr assign1 assign2 aig rhs (by omega) h]

end AIG
