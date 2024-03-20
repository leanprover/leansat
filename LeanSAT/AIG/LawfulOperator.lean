/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.AIG.Basic
import LeanSAT.AIG.Lemmas

/-!
The lawful operator framework provides a large amount of free theorems around the typeclasses
`LawfulUnaryOperator` and `LawfulBinaryOperator`. Their definitions are based on section 3.3 of
the AIGNET paper.
-/

namespace AIG

abbrev UnaryOperator :=
    {α : Type} → [BEq α] → [Hashable α] → [DecidableEq α] →
      (gate : Nat) → (aig : AIG α) → (gate < aig.decls.size) → Entrypoint α

class LawfulUnaryOperator (f : UnaryOperator) where
  le_size {α : Type} [BEq α] [Hashable α] [DecidableEq α] : ∀ (aig : AIG α) (gate : Nat) (hgate),
    aig.decls.size ≤ (f gate aig hgate).aig.decls.size
  decl_eq {α : Type} [BEq α] [Hashable α] [DecidableEq α] : ∀ (aig : AIG α) (gate : Nat) (idx : Nat)
      (h1 : idx < aig.decls.size) (hgate) (h2),
        (f gate aig hgate).aig.decls[idx]'h2 = aig.decls[idx]'h1

namespace LawfulUnaryOperator

variable {f : UnaryOperator} [LawfulUnaryOperator f]
variable {α : Type} [BEq α] [Hashable α] [DecidableEq α]

theorem IsPrefix_aig (aig : AIG α) (gate : Nat) {hgate} :
    IsPrefix aig.decls (f gate aig hgate).aig.decls := by
  apply IsPrefix.of
  . intro idx h
    apply decl_eq
  . apply le_size

theorem lt_mkNotCached_size (entry : Entrypoint α) (gate : Nat) (hgate) :
    entry.start < (f gate entry.aig hgate).aig.decls.size := by
  have h1 := entry.inv
  have h2 : entry.aig.decls.size ≤ (f gate entry.aig hgate).aig.decls.size := by
    apply le_size
  omega

theorem lt_size_of_lt_aig_size (aig : AIG α) (gate : Nat) (hgate) (h : x < aig.decls.size)
    : x < (f gate aig hgate).aig.decls.size := by
  apply Nat.lt_of_lt_of_le
  . exact h
  . exact le_size aig gate hgate

theorem le_size_of_le_aig_size (aig : AIG α) (gate : Nat) (hgate) (h : x ≤ aig.decls.size)
    : x ≤ (f gate aig hgate).aig.decls.size := by
  apply Nat.le_trans
  . exact h
  . exact le_size aig gate hgate

@[simp]
theorem denote_entry (entry : Entrypoint α) {hgate} {h} :
    ⟦(f gate entry.aig hgate).aig, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_aig_eq
  apply IsPrefix_aig

theorem denote_mem_prefix {aig : AIG α} {hgate} (h) :
    ⟦(f gate aig hgate).aig, ⟨start, by apply lt_size_of_lt_aig_size; omega⟩, assign⟧
      =
    ⟦aig, ⟨start, h⟩, assign⟧ :=  by
  rw [denote_entry ⟨aig, start, h⟩]

end LawfulUnaryOperator

abbrev BinaryOperator :=
    {α : Type} → [BEq α] → [Hashable α] → [DecidableEq α] →
      (lhs rhs : Nat) → (aig : AIG α) → (lhs < aig.decls.size) → (rhs < aig.decls.size) → Entrypoint α

class LawfulBinaryOperator (f : BinaryOperator) where
  le_size {α : Type} [BEq α] [Hashable α] [DecidableEq α] : ∀ (aig : AIG α) (lhs rhs : Nat) (hl) (hr),
    aig.decls.size ≤ (f lhs rhs aig hl hr).aig.decls.size
  decl_eq {α : Type} [BEq α] [Hashable α] [DecidableEq α] : ∀ (aig : AIG α) (lhs rhs : Nat) (idx : Nat)
    (h1 : idx < aig.decls.size) (hl) (hr) (h2),
      (f lhs rhs aig hl hr).aig.decls[idx]'h2 = aig.decls[idx]'h1

namespace LawfulBinaryOperator

variable {f : BinaryOperator} [LawfulBinaryOperator f]
variable {α : Type} [BEq α] [Hashable α] [DecidableEq α]

theorem IsPrefix_aig (aig : AIG α) (lhs rhs : Nat) {hl} {hr} :
    IsPrefix aig.decls (f lhs rhs aig hl hr).aig.decls := by
  apply IsPrefix.of
  . intro idx h
    apply decl_eq
  . apply le_size

theorem lt_size (entry : Entrypoint α) (lhs hrs : Nat) (hl) (hr)
    : entry.start < (f lhs rhs entry.aig hl hr).aig.decls.size := by
  have h1 := entry.inv
  have h2 : entry.aig.decls.size ≤ (f lhs rhs entry.aig hl hr).aig.decls.size := by
    apply le_size
  omega

theorem lt_size_of_lt_aig_size (aig : AIG α) (lhs rhs : Nat) (hl hr)
    (h : x < aig.decls.size)
    : x < (f lhs rhs aig hl hr).aig.decls.size := by
  apply Nat.lt_of_lt_of_le
  . exact h
  . exact le_size aig lhs rhs hl hr

@[simp]
theorem denote_entry (entry : Entrypoint α) {hl} {hr} {h} :
    ⟦(f lhs rhs entry.aig hl hr).aig, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_aig_eq
  apply IsPrefix_aig

theorem denote_mem_prefix {aig : AIG α} {hl} {hr} (h) :
    ⟦(f lhs rhs aig hl hr).aig, ⟨start, (by apply lt_size_of_lt_aig_size; omega)⟩, assign⟧
      =
    ⟦aig, ⟨start, h⟩, assign⟧ :=  by
  rw [denote_entry ⟨aig, start, h⟩]

end LawfulBinaryOperator

end AIG
