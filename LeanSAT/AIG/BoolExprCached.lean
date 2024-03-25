/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.AIG.CachedGates
import LeanSAT.AIG.CachedGatesLemmas

/-!
This module contains the logic to turn a `BoolExpr Nat` into an `AIG` with maximum subterm sharing,
through the use of a cache that re-uses sub-circuits if possible.
-/

namespace AIG

variable {α : Type} [BEq α] [Hashable α] [DecidableEq α]

-- lines such as: ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩
-- are slow in Meta.check
-- TODO: minimize
/--
Turn a `BoolExpr` into an AIG + entrypoint.
-/
def ofBoolExprCached (expr : BoolExpr α) : Entrypoint α :=
  go expr AIG.empty |>.val
where
  go (expr : BoolExpr α) (aig : AIG α) : { entry : Entrypoint α // aig.decls.size ≤ entry.aig.decls.size } :=
    match expr with
    | .literal var => ⟨aig.mkAtomCached var, (by apply AIG.mkAtomCached_le_size)⟩
    | .const val => ⟨aig.mkConstCached val, (by apply AIG.mkConstCached_le_size)⟩
    | .not expr =>
      let ⟨exprEntry, _⟩ := go expr aig
      let exprRef := Ref.ofEntrypoint exprEntry
      let ret := exprEntry.aig.mkNotCached exprRef
      have := LawfulOperator.le_size (f := mkNotCached) exprEntry.aig exprRef
      ⟨ret, by dsimp [ret] at *; omega⟩
    | .gate g lhs rhs =>
      let ⟨lhsEntry, _⟩ := go lhs aig
      let ⟨rhsEntry, _⟩ := go rhs lhsEntry.aig
      let lhsRef := Ref.ofEntrypoint lhsEntry |>.cast (by omega)
      let rhsRef := Ref.ofEntrypoint rhsEntry
      let input := ⟨lhsRef, rhsRef⟩
      match g with
      | .and =>
        let ret := rhsEntry.aig.mkAndCached input
        have := LawfulOperator.le_size (f := mkAndCached) rhsEntry.aig input
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .or =>
        let ret := rhsEntry.aig.mkOrCached input
        have := LawfulOperator.le_size (f := mkOrCached) rhsEntry.aig input
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .xor =>
        let ret := rhsEntry.aig.mkXorCached input
        have := LawfulOperator.le_size (f := mkXorCached) rhsEntry.aig input
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .beq =>
        let ret := rhsEntry.aig.mkBEqCached input
        have := LawfulOperator.le_size (f := mkBEqCached) rhsEntry.aig input
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .imp =>
        let ret := rhsEntry.aig.mkImpCached input
        have := LawfulOperator.le_size (f := mkImpCached) rhsEntry.aig input
        ⟨ret, by dsimp [ret] at *; omega⟩

theorem ofBoolExprCached.go_decls_size_le (expr : BoolExpr α) (aig : AIG α) :
    aig.decls.size ≤ (ofBoolExprCached.go expr aig).val.aig.decls.size := by
  exact (ofBoolExprCached.go expr aig).property

theorem ofBoolExprCached.go_decl_eq (idx) (aig : AIG α) (h : idx < aig.decls.size) (hbounds) :
    (ofBoolExprCached.go expr aig).val.aig.decls[idx]'hbounds = aig.decls[idx] := by
  induction expr generalizing aig with
  | const =>
    simp only [go]
    apply mkConstCached_decl_eq
  | literal =>
    simp only [go]
    apply mkAtomCached_decl_eq
  | not expr ih =>
    simp only [go]
    have := go_decls_size_le expr aig
    specialize ih aig (by omega) (by omega)
    rw [mkNotCached_decl_eq]
    assumption
  | gate g lhs rhs lih rih =>
    have := go_decls_size_le lhs aig
    have := go_decls_size_le rhs (go lhs aig).val.aig
    specialize lih aig (by omega) (by omega)
    specialize rih (go lhs aig).val.aig (by omega) (by omega)
    cases g with
    | and =>
      simp only [go]
      rw [mkAndCached_decl_eq]
      rw [rih, lih]
    | or =>
      simp only [go]
      rw [mkOrCached_decl_eq]
      rw [rih, lih]
    | xor =>
      simp only [go]
      rw [mkXorCached_decl_eq]
      rw [rih, lih]
    | beq =>
      simp only [go]
      rw [mkBEqCached_decl_eq]
      rw [rih, lih]
    | imp =>
      simp only [go]
      rw [mkImpCached_decl_eq]
      rw [rih, lih]

theorem ofBoolExprCached.go_IsPrefix_aig {aig : AIG α} : IsPrefix aig.decls (go expr aig).val.aig.decls := by
  apply IsPrefix.of
  . intro idx h
    apply ofBoolExprCached.go_decl_eq
  . apply ofBoolExprCached.go_decls_size_le

@[simp]
theorem ofBoolExprCached.go_denote_entry (entry : Entrypoint α) {h}:
    ⟦(go expr entry.aig).val.aig, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ := by
  apply denote.eq_of_aig_eq
  apply ofBoolExprCached.go_IsPrefix_aig

@[simp]
theorem ofBoolExprCached.go_eval_eq_eval (expr : BoolExpr α) (aig : AIG α) (assign) :
    ⟦go expr aig, assign⟧ = expr.eval assign := by
  induction expr generalizing aig with
  | const => simp [go]
  | literal => simp [go]
  | not expr ih => simp [go, ih]
  | gate g lhs rhs lih rih => cases g <;> simp [go, Gate.eval, lih, rih]

@[simp]
theorem ofBoolExprCached_eval_eq_eval (expr : BoolExpr α) (assign) :
    ⟦ofBoolExprCached expr, assign⟧ = expr.eval assign := by
  apply ofBoolExprCached.go_eval_eq_eval

theorem ofBoolExprCached_unsat_iff {expr : BoolExpr α} : (ofBoolExprCached expr).unsat ↔ expr.unsat := by
  constructor
  all_goals
    intro h assign
    specialize h assign
    simpa using h

end AIG
