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

-- lines such as: ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩
-- are slow in Meta.check
-- TODO: minimize
/--
Turn a `BoolExprNat` into an AIG + entrypoint. Note that this version is meant for programming
purposes. For proving use `AIG.ofBoolExprNat` and equality theorems.
-/
def ofBoolExprNatCached (expr : BoolExpr Nat) : Entrypoint :=
  go expr AIG.empty |>.val
where
  go (expr : BoolExpr Nat) (aig : AIG) : { entry : Entrypoint // aig.decls.size ≤ entry.aig.decls.size } :=
    match expr with
    | .literal var => ⟨aig.mkAtomCached var, (by apply AIG.mkAtomCached_le_size)⟩
    | .const val => ⟨aig.mkConstCached val, (by apply AIG.mkConstCached_le_size)⟩
    | .not expr =>
      let ⟨exprEntry, _⟩ := go expr aig
      let ret := exprEntry.aig.mkNotCached exprEntry.start exprEntry.inv
      have := mkNotCached_le_size exprEntry.aig exprEntry.start exprEntry.inv
      ⟨ret, by dsimp [ret] at *; omega⟩
    | .gate g lhs rhs =>
      let ⟨lhsEntry, _⟩ := go lhs aig
      let ⟨rhsEntry, _⟩ := go rhs lhsEntry.aig
      have h1 : lhsEntry.start < Array.size rhsEntry.aig.decls := by
        have := lhsEntry.inv
        omega
      match g with
      | .and =>
        let ret := rhsEntry.aig.mkAndCached lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkAndCached_le_size rhsEntry.aig lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .or =>
        let ret := rhsEntry.aig.mkOrCached lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkOrCached_le_size rhsEntry.aig lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .xor =>
        let ret := rhsEntry.aig.mkXorCached lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkXorCached_le_size rhsEntry.aig lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .beq =>
        let ret := rhsEntry.aig.mkBEqCached lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkBEqCached_le_size rhsEntry.aig lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .imp =>
        let ret := rhsEntry.aig.mkImpCached lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkImpCached_le_size rhsEntry.aig lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩

theorem ofBoolExprNatCached.go_decls_size_le (expr : BoolExpr Nat) (aig : AIG) :
    aig.decls.size ≤ (ofBoolExprNatCached.go expr aig).val.aig.decls.size := by
  exact (ofBoolExprNatCached.go expr aig).property

theorem ofBoolExprNatCached.go_decl_eq (idx) (aig) (h : idx < aig.decls.size) (hbounds) :
    (ofBoolExprNatCached.go expr aig).val.aig.decls[idx]'hbounds = aig.decls[idx] := by
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

theorem ofBoolExprNatCached.go_IsPrefix_aig : IsPrefix aig.decls (go expr aig).val.aig.decls := by
  apply IsPrefix.of
  . intro idx h
    apply ofBoolExprNatCached.go_decl_eq
  . apply ofBoolExprNatCached.go_decls_size_le

@[simp]
theorem ofBoolExprNatCached.go_denote_entry (entry : Entrypoint) {h}:
    ⟦(go expr entry.aig).val.aig, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ := by
  apply denote.eq_of_aig_eq
  apply ofBoolExprNatCached.go_IsPrefix_aig

@[simp]
theorem ofBoolExprNatCached.go_eval_eq_eval (expr : BoolExpr Nat) (aig : AIG) (assign) :
    ⟦go expr aig, assign⟧ = expr.eval assign := by
  induction expr generalizing aig with
  | const => simp [go]
  | literal => simp [go]
  | not expr ih => simp [go, ih]
  | gate g lhs rhs lih rih => cases g <;> simp [go, Gate.eval, lih, rih]

@[simp]
theorem ofBoolExprCached_eval_eq_eval (expr : BoolExpr Nat) (assign) :
    ⟦ofBoolExprNatCached expr, assign⟧ = expr.eval assign := by
  apply ofBoolExprNatCached.go_eval_eq_eval

theorem ofBoolExprCached_unsat_iff : (ofBoolExprNatCached expr).unsat ↔ expr.unsat := by
  constructor
  all_goals
    intro h assign
    specialize h assign
    simpa using h

end AIG
