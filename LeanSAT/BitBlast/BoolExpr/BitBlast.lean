/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.AIG.CachedGates
import LeanSAT.AIG.CachedGatesLemmas
import LeanSAT.BitBlast.BoolExpr.Basic

/-!
This module contains the logic to turn a `BoolExpr Nat` into an `AIG` with maximum subterm sharing,
through the use of a cache that re-uses sub-circuits if possible.
-/

namespace AIG

variable {β : Type} [Hashable β] [DecidableEq β]


/--
Turn a `BoolExpr` into an AIG + entrypoint.
-/
def ofBoolExprCached (expr : BoolExpr α) (atomHandler : AIG β → α → Entrypoint β)
    [LawfulOperator β (fun _ => α) atomHandler] : Entrypoint β :=
  go expr AIG.empty atomHandler |>.val
where
  go (expr : BoolExpr α) (aig : AIG β) (atomHandler : AIG β → α → Entrypoint β)
      [LawfulOperator β (fun _ => α) atomHandler]
      : ExtendingEntrypoint aig :=
    match expr with
    | .literal var => ⟨atomHandler aig var, by apply LawfulOperator.le_size⟩
    | .const val => ⟨aig.mkConstCached val, (by apply LawfulOperator.le_size)⟩
    | .not expr =>
      let ⟨⟨aig, exprRef⟩, _⟩ := go expr aig atomHandler
      let ret := aig.mkNotCached exprRef
      have := LawfulOperator.le_size (f := mkNotCached) aig exprRef
      ⟨ret, by dsimp [ret] at *; omega⟩
    | .gate g lhs rhs =>
      let ⟨⟨aig, lhsRef⟩, lextend⟩ := go lhs aig atomHandler
      let ⟨⟨aig, rhsRef⟩, rextend⟩ := go rhs aig atomHandler
      let lhsRef := lhsRef.cast <| by
        dsimp at rextend ⊢
        omega
      let input := ⟨lhsRef, rhsRef⟩
      match g with
      | .and =>
        let ret := aig.mkAndCached input
        have := LawfulOperator.le_size (f := mkAndCached) aig input
        -- TODO: why two dsimp calls???????
        ⟨ret, by dsimp [ret] at *; dsimp at rextend; omega⟩
      | .or =>
        let ret := aig.mkOrCached input
        have := LawfulOperator.le_size (f := mkOrCached) aig input
        ⟨ret, by dsimp [ret] at *; dsimp at rextend; omega⟩
      | .xor =>
        let ret := aig.mkXorCached input
        have := LawfulOperator.le_size (f := mkXorCached) aig input
        ⟨ret, by dsimp [ret] at *; dsimp at rextend; omega⟩
      | .beq =>
        let ret := aig.mkBEqCached input
        have := LawfulOperator.le_size (f := mkBEqCached) aig input
        ⟨ret, by dsimp [ret] at *; dsimp at rextend; omega⟩
      | .imp =>
        let ret := aig.mkImpCached input
        have := LawfulOperator.le_size (f := mkImpCached) aig input
        ⟨ret, by dsimp [ret] at *; dsimp at rextend; omega⟩


variable (atomHandler : AIG β → α → Entrypoint β) [LawfulOperator β (fun _ => α) atomHandler]

theorem ofBoolExprCached.go_decls_size_le (expr : BoolExpr α) (aig : AIG β) :
    aig.decls.size ≤ (ofBoolExprCached.go expr aig atomHandler).val.aig.decls.size := by
  exact (ofBoolExprCached.go expr aig atomHandler).property

theorem ofBoolExprCached.go_decl_eq (idx) (aig : AIG β) (h : idx < aig.decls.size) (hbounds) :
    (ofBoolExprCached.go expr aig atomHandler).val.aig.decls[idx]'hbounds = aig.decls[idx] := by
  induction expr generalizing aig with
  | const =>
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := mkConstCached)]
  | literal =>
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := atomHandler)]
  | not expr ih =>
    simp only [go]
    have := go_decls_size_le atomHandler expr aig
    specialize ih aig (by omega) (by omega)
    rw [AIG.LawfulOperator.decl_eq (f := mkNotCached)]
    assumption
  | gate g lhs rhs lih rih =>
    have := go_decls_size_le atomHandler lhs aig
    have := go_decls_size_le atomHandler rhs (go lhs aig atomHandler).val.aig
    specialize lih aig (by omega) (by omega)
    specialize rih (go lhs aig atomHandler).val.aig (by omega) (by omega)
    cases g with
    | and =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkAndCached)]
      rw [rih, lih]
    | or =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkOrCached)]
      rw [rih, lih]
    | xor =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkXorCached)]
      rw [rih, lih]
    | beq =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkBEqCached)]
      rw [rih, lih]
    | imp =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkImpCached)]
      rw [rih, lih]

theorem ofBoolExprCached.go_IsPrefix_aig {aig : AIG β}
    : IsPrefix aig.decls (go expr aig atomHandler).val.aig.decls := by
  apply IsPrefix.of
  . intro idx h
    apply ofBoolExprCached.go_decl_eq
  . apply ofBoolExprCached.go_decls_size_le


@[simp]
theorem ofBoolExprCached.go_denote_entry (entry : Entrypoint β) {h}:
    ⟦(go expr entry.aig atomHandler).val.aig, ⟨entry.ref.gate, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ := by
  apply denote.eq_of_aig_eq
  apply ofBoolExprCached.go_IsPrefix_aig

variable {α : Type} [Hashable α] [DecidableEq α]
def ofBoolExprCachedDirect (expr : BoolExpr α) : Entrypoint α :=
  ofBoolExprCached expr mkAtomCached

@[simp]
theorem ofBoolExprCached.go_eval_eq_eval (expr : BoolExpr α) (aig : AIG α) (assign) :
    ⟦go expr aig mkAtomCached, assign⟧ = expr.eval assign := by
  induction expr generalizing aig with
  | const => simp [go]
  | literal => simp [go]
  | not expr ih => simp [go, ih]
  | gate g lhs rhs lih rih => cases g <;> simp [go, Gate.eval, lih, rih]

@[simp]
theorem ofBoolExprCachedDirect_eval_eq_eval (expr : BoolExpr α) (assign) :
    ⟦ofBoolExprCachedDirect expr, assign⟧ = expr.eval assign := by
  apply ofBoolExprCached.go_eval_eq_eval

theorem ofBoolExprCachedDirect_unsat_iff {expr : BoolExpr α} : (ofBoolExprCachedDirect expr).unsat ↔ expr.unsat := by
  constructor
  all_goals
    intro h assign
    specialize h assign
    simpa using h

end AIG
