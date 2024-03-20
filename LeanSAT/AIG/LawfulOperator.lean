/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.AIG.Basic
import LeanSAT.AIG.Lemmas

namespace AIG

abbrev UnaryOperator := (gate : Nat) → (aig : AIG) → (gate < aig.decls.size) → Entrypoint

class LawfulUnaryOperator (f : UnaryOperator) where
  le_size : ∀ (aig : AIG) (gate : Nat) (hgate), aig.decls.size ≤ (f gate aig hgate).aig.decls.size
  decl_eq : ∀ (aig : AIG) (gate : Nat) (idx : Nat) (h1 : idx < aig.decls.size) (hgate) (h2),
    (f gate aig hgate).aig.decls[idx]'h2 = aig.decls[idx]'h1

namespace LawfulUnaryOperator

variable {f : UnaryOperator} [LawfulUnaryOperator f]

theorem IsPrefix_aig (aig : AIG) (gate : Nat) {hgate} :
    IsPrefix aig.decls (f gate aig hgate).aig.decls := by
  apply IsPrefix.of
  . intro idx h
    apply decl_eq
  . apply le_size

theorem lt_mkNotCached_size (entry : Entrypoint) (gate : Nat) (hgate) :
    entry.start < (f gate entry.aig hgate).aig.decls.size := by
  have h1 := entry.inv
  have h2 : entry.aig.decls.size ≤ (f gate entry.aig hgate).aig.decls.size := by
    apply le_size
  omega

theorem lt_size_of_lt_aig_size (aig : AIG) (gate : Nat) (hgate) (h : x < aig.decls.size)
    : x < (f gate aig hgate).aig.decls.size := by
  have := le_size (f := f) aig gate hgate
  omega

theorem le_size_of_le_aig_size (aig : AIG) (gate : Nat) (hgate) (h : x ≤ aig.decls.size)
    : x ≤ (f gate aig hgate).aig.decls.size := by
  have := le_size (f := f) aig gate hgate
  omega

@[simp]
theorem denote_entry (entry : Entrypoint) {hgate} {h} :
    ⟦(f gate entry.aig hgate).aig, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_aig_eq
  apply IsPrefix_aig

theorem denote_mem_prefix {aig : AIG} {hgate} (h) :
    ⟦(f gate aig hgate).aig, ⟨start, by apply lt_size_of_lt_aig_size; omega⟩, assign⟧
      =
    ⟦aig, ⟨start, h⟩, assign⟧ :=  by
  rw [denote_entry ⟨aig, start, h⟩]

end LawfulUnaryOperator

abbrev BinaryOperator := (lhs rhs : Nat) → (aig : AIG) → (lhs < aig.decls.size) → (rhs < aig.decls.size) → Entrypoint

class LawfulBinaryOperator (f : BinaryOperator) where
  le_size : ∀ (aig : AIG) (lhs rhs : Nat) (hl) (hr), aig.decls.size ≤ (f lhs rhs aig hl hr).aig.decls.size
  decl_eq : ∀ (aig : AIG) (lhs rhs : Nat) (idx : Nat) (h1 : idx < aig.decls.size) (hl) (hr) (h2),
    (f lhs rhs aig hl hr).aig.decls[idx]'h2 = aig.decls[idx]'h1

namespace LawfulBinaryOperator

variable {f : BinaryOperator} [LawfulBinaryOperator f]

theorem IsPrefix_aig (aig : AIG) (lhs rhs : Nat) {hl} {hr} :
    IsPrefix aig.decls (f lhs rhs aig hl hr).aig.decls := by
  apply IsPrefix.of
  . intro idx h
    apply decl_eq
  . apply le_size

theorem lt_size (entry : Entrypoint) (lhs hrs : Nat) (hl) (hr)
    : entry.start < (f lhs rhs entry.aig hl hr).aig.decls.size := by
  have h1 := entry.inv
  have h2 : entry.aig.decls.size ≤ (f lhs rhs entry.aig hl hr).aig.decls.size := by
    apply le_size
  omega

theorem lt_size_of_lt_aig_size (aig : AIG) (lhs rhs : Nat) (hl hr)
    (h : x < aig.decls.size)
    : x < (f lhs rhs aig hl hr).aig.decls.size := by
  have := le_size (f := f) aig lhs rhs hl hr
  omega

@[simp]
theorem denote_entry (entry : Entrypoint) {hl} {hr} {h} :
    ⟦(f lhs rhs entry.aig hl hr).aig, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_aig_eq
  apply IsPrefix_aig

theorem denote_mem_prefix {aig : AIG} {hl} {hr} (h) :
    ⟦(f lhs rhs aig hl hr).aig, ⟨start, (by apply lt_size_of_lt_aig_size; omega)⟩, assign⟧
      =
    ⟦aig, ⟨start, h⟩, assign⟧ :=  by
  rw [denote_entry ⟨aig, start, h⟩]

end LawfulBinaryOperator

end AIG
