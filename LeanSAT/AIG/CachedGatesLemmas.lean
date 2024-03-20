/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.AIG.CachedGates
import LeanSAT.AIG.LawfulOperator

/-!
This module contains the theory of the cached gate creation functions, mostly enabled by the
`LawfulOperator` framework. It is mainly concerned with proving lemmas about the denotational
semantics of the gate functions in different scenarios.
-/

/--
Encoding not as boolen expression in AIG form.
-/
theorem not_as_aig (b : Bool) : (true && !b) = !b := by cases b <;> decide

/--
Encoding or as boolen expression in AIG form.
-/
theorem or_as_aig (a b : Bool) : (!(!a && !b)) = (a || b) := by cases a <;> cases b <;> decide

/--
Encoding XOR as boolen expression in AIG form.
-/
theorem xor_as_aig (a b : Bool) : (!(a && b) && !(!a && !b)) = (xor a b) := by cases a <;> cases b <;> decide

/--
Encoding BEq as boolen expression in AIG form.
-/
theorem beq_as_aig (a b : Bool) : (!(a && !b) && !(!a && b)) = (a == b) := by cases a <;> cases b <;> decide

/--
Encoding implication as boolen expression in AIG form.
-/
theorem imp_as_aig (a b : Bool) : (!(a && !b)) = (!a || b) := by cases a <;> cases b <;> decide

namespace AIG

theorem mkNotCached_le_size (aig : AIG) (gate : Nat) (hgate)
    : aig.decls.size ≤ (aig.mkNotCached gate hgate).aig.decls.size := by
  simp only [mkNotCached]
  apply le_mkGateCached_size_of_le_aig_size
  apply mkConstCached_le_size

theorem mkNotCached_decl_eq idx (aig : AIG) (gate : Nat) {h : idx < aig.decls.size} (hgate) {h2} :
    (aig.mkNotCached gate hgate).aig.decls[idx]'h2 = aig.decls[idx] := by
  simp only [mkNotCached]
  rw [mkGateCached_decl_eq]
  rw [mkConstCached_decl_eq]
  apply lt_mkConstCached_size_of_lt_aig_size
  assumption

instance : LawfulUnaryOperator mkNotCached where
  le_size := mkNotCached_le_size
  decl_eq := by
    intros
    apply mkNotCached_decl_eq

@[simp]
theorem denote_mkNotCached {aig : AIG} {hgate} :
    ⟦aig.mkNotCached gate hgate, assign⟧
      =
    !⟦aig, ⟨gate, hgate⟩, assign⟧ := by
  rw [← not_as_aig]
  simp [mkNotCached, denote_mkConstCached_mem_prefix hgate]


theorem mkAndCached_le_size (aig : AIG) (lhs rhs : Nat) (hl) (hr)
    : aig.decls.size ≤ (aig.mkAndCached lhs rhs hl hr).aig.decls.size := by
  simp only [mkAndCached]
  apply le_mkGateCached_size_of_le_aig_size
  omega

theorem mkAndCached_decl_eq idx (aig : AIG) (lhs rhs : Nat) {h : idx < aig.decls.size}
    (hl) (hr) {h2} :
    (aig.mkAndCached lhs rhs hl hr).aig.decls[idx]'h2 = aig.decls[idx] := by
  simp only [mkAndCached]
  rw [mkGateCached_decl_eq]

instance : LawfulBinaryOperator mkAndCached where
  le_size := mkAndCached_le_size
  decl_eq := by intros; apply mkAndCached_decl_eq

@[simp]
theorem denote_mkAndCached {aig : AIG} {hl} {hr} :
    ⟦aig.mkAndCached lhs rhs hl hr, assign⟧
      =
    (⟦aig, ⟨lhs, hl⟩, assign⟧ && ⟦aig, ⟨rhs, hr⟩, assign⟧) := by
  simp [mkAndCached]

theorem mkOrCached_le_size (aig : AIG) (lhs rhs : Nat) (hl) (hr)
    : aig.decls.size ≤ (aig.mkOrCached lhs rhs hl hr).aig.decls.size := by
  simp only [mkOrCached]
  apply le_mkGateCached_size_of_le_aig_size
  apply le_mkConstCached_size_of_le_aig_size
  apply le_mkGateCached_size_of_le_aig_size
  omega

theorem mkOrCached_decl_eq idx (aig : AIG) (lhs rhs : Nat) {h : idx < aig.decls.size}
    (hl) (hr) {h2} :
    (aig.mkOrCached lhs rhs hl hr).aig.decls[idx]'h2 = aig.decls[idx] := by
  simp only [mkOrCached]
  rw [mkGateCached_decl_eq]
  rw [mkConstCached_decl_eq]
  . rw [mkGateCached_decl_eq]
    apply lt_mkGateCached_size_of_lt_aig_size
    assumption
  . apply lt_mkConstCached_size_of_lt_aig_size
    apply lt_mkGateCached_size_of_lt_aig_size
    assumption

instance : LawfulBinaryOperator mkOrCached where
  le_size := mkOrCached_le_size
  decl_eq := by intros; apply mkOrCached_decl_eq

@[simp]
theorem denote_mkOrCached {aig : AIG} {hl} {hr}:
    ⟦aig.mkOrCached lhs rhs hl hr, assign⟧
      =
    (⟦aig, ⟨lhs, hl⟩, assign⟧ || ⟦aig, ⟨rhs, hr⟩, assign⟧) := by
  rw [← or_as_aig]
  simp [mkOrCached]

theorem mkXorCached_le_size (aig : AIG) (lhs rhs : Nat) (hl) (hr)
    : aig.decls.size ≤ (aig.mkXorCached lhs rhs hl hr).aig.decls.size := by
  simp only [mkXorCached]
  apply le_mkGateCached_size_of_le_aig_size
  apply le_mkGateCached_size_of_le_aig_size
  apply le_mkGateCached_size_of_le_aig_size
  omega

theorem mkXorCached_decl_eq idx (aig : AIG) (lhs rhs : Nat) {h : idx < aig.decls.size}
    (hl) (hr) {h2} :
    (aig.mkXorCached lhs rhs hl hr).aig.decls[idx]'h2 = aig.decls[idx] := by
  simp only [mkXorCached]
  rw [mkGateCached_decl_eq]
  rw [mkGateCached_decl_eq]
  . rw [mkGateCached_decl_eq]
    apply lt_mkGateCached_size_of_lt_aig_size
    assumption
  . apply lt_mkGateCached_size_of_lt_aig_size
    apply lt_mkGateCached_size_of_lt_aig_size
    assumption

instance : LawfulBinaryOperator mkXorCached where
  le_size := mkXorCached_le_size
  decl_eq := by intros; apply mkXorCached_decl_eq

@[simp]
theorem denote_mkXorCached {aig : AIG} {hl} {hr} :
    ⟦aig.mkXorCached lhs rhs hl hr, assign⟧
      =
    xor ⟦aig, ⟨lhs, hl⟩, assign⟧ ⟦aig, ⟨rhs, hr⟩, assign⟧ := by
  rw [← xor_as_aig]
  simp [mkXorCached, denote_mkGateCached_mem_prefix hl, denote_mkGateCached_mem_prefix hr]

theorem mkBEqCached_le_size (aig : AIG) (lhs rhs : Nat) (hl) (hr)
    : aig.decls.size ≤ (aig.mkBEqCached lhs rhs hl hr).aig.decls.size := by
  simp only [mkBEqCached]
  apply le_mkGateCached_size_of_le_aig_size
  apply le_mkGateCached_size_of_le_aig_size
  apply le_mkGateCached_size_of_le_aig_size
  omega

theorem mkBEqCached_decl_eq idx (aig : AIG) (lhs rhs : Nat) {h : idx < aig.decls.size}
    (hl) (hr) {h2} :
    (aig.mkBEqCached lhs rhs hl hr).aig.decls[idx]'h2 = aig.decls[idx] := by
  simp only [mkBEqCached]
  rw [mkGateCached_decl_eq]
  rw [mkGateCached_decl_eq]
  . rw [mkGateCached_decl_eq]
    apply lt_mkGateCached_size_of_lt_aig_size
    assumption
  . apply lt_mkGateCached_size_of_lt_aig_size
    apply lt_mkGateCached_size_of_lt_aig_size
    assumption

instance : LawfulBinaryOperator mkBEqCached where
  le_size := mkBEqCached_le_size
  decl_eq := by intros; apply mkBEqCached_decl_eq

@[simp]
theorem denote_mkBEqCached {aig : AIG} {hl} {hr} :
    ⟦aig.mkBEqCached lhs rhs hl hr, assign⟧
      =
    (⟦aig, ⟨lhs, hl⟩, assign⟧ == ⟦aig, ⟨rhs, hr⟩, assign⟧) := by
  rw [← beq_as_aig]
  simp [mkBEqCached, denote_mkGateCached_mem_prefix hl, denote_mkGateCached_mem_prefix hr]

theorem mkImpCached_le_size (aig : AIG) (lhs rhs : Nat) (hl) (hr)
    : aig.decls.size ≤ (aig.mkImpCached lhs rhs hl hr).aig.decls.size := by
  simp only [mkImpCached]
  apply le_mkGateCached_size_of_le_aig_size
  apply le_mkConstCached_size_of_le_aig_size
  apply le_mkGateCached_size_of_le_aig_size
  omega

theorem mkImpCached_decl_eq idx (aig : AIG) (lhs rhs : Nat) {h : idx < aig.decls.size}
    (hl) (hr) {h2} :
    (aig.mkImpCached lhs rhs hl hr).aig.decls[idx]'h2 = aig.decls[idx] := by
  simp only [mkImpCached]
  rw [mkGateCached_decl_eq]
  rw [mkConstCached_decl_eq]
  . rw [mkGateCached_decl_eq]
    apply lt_mkGateCached_size_of_lt_aig_size
    assumption
  . apply lt_mkConstCached_size_of_lt_aig_size
    apply lt_mkGateCached_size_of_lt_aig_size
    assumption

instance : LawfulBinaryOperator mkImpCached where
  le_size := mkImpCached_le_size
  decl_eq := by intros; apply mkImpCached_decl_eq

@[simp]
theorem denote_mkImpCached {aig : AIG} {hl} {hr} :
    ⟦aig.mkImpCached lhs rhs hl hr, assign⟧
      =
    (!⟦aig, ⟨lhs, hl⟩, assign⟧ || ⟦aig, ⟨rhs, hr⟩, assign⟧) := by
  rw [← imp_as_aig]
  simp [mkImpCached]

end AIG
