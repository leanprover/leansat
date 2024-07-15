/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.CNF.RelabelFin

import LeanSAT.LRAT.LRATChecker

open Lean Elab Meta

/--
Turn a `CNF Nat`, that might contain `0` as a variable, to a `CNF PosFin`.
This representation is guaranteed to not have `0` and is limited to an upper bound of
variable indices.
-/
def CNF.lift (cnf : CNF Nat) : CNF (PosFin (cnf.numLiterals + 1)) :=
  let cnf := cnf.relabelFin
  cnf.relabel (fun lit => ⟨lit.val + 1, by omega⟩)

theorem CNF.unsat_of_lift_unsat (cnf : CNF Nat) : CNF.unsat cnf.lift → CNF.unsat cnf := by
  intro h2
  have h3 :=
    CNF.unsat_relabel_iff
      (by
        intro a b ha hb hab
        injections hab
        cases a; cases b; simp_all)
      |>.mp h2
  exact CNF.unsat_relabelFin.mp h3

/--
Turn a `CNF.Clause PosFin` into the representation used by the LRAT checker.
-/
def CNF.Clause.convertLRAT' (clause : CNF.Clause (PosFin n)) : Option (LRAT.DefaultClause n) :=
  LRAT.DefaultClause.ofArray clause.toArray

/--
Turn a `CNF PosFin` into the representation used by the LRAT checker.
-/
def CNF.convertLRAT' (clauses : CNF (PosFin n)) : List (Option (LRAT.DefaultClause n)) :=
  clauses.filterMap (fun clause =>
    match CNF.Clause.convertLRAT' clause with
    | some foo => some foo
    | none => none
  )

theorem CNF.Clause.mem_lrat_of_mem (clause : CNF.Clause (PosFin n)) (h1 : l ∈ clause)
    (h2 : LRAT.DefaultClause.ofArray clause.toArray = some lratClause) : l ∈ lratClause.clause := by
  induction clause generalizing lratClause with
  | nil => cases h1
  | cons hd tl ih =>
    unfold LRAT.DefaultClause.ofArray at h2
    rw [Array.foldr_eq_foldr_data,Array.toArray_data] at h2
    dsimp only [List.foldr] at h2
    split at h2
    · cases h2
    · rw [LRAT.DefaultClause.insert] at h2
      split at h2
      · cases h2
      · split at h2
        · rename_i h
          rw [<-Option.some.inj h2] at *
          cases h1
          · exact List.mem_of_elem_eq_true h
          · apply ih
            · assumption
            · next heq _ _ =>
              unfold LRAT.DefaultClause.ofArray
              rw [Array.foldr_eq_foldr_data,Array.toArray_data]
              exact heq
        · cases h1
          · simp only [<-Option.some.inj h2]
            constructor
          · simp only at h2
            simp only [<-Option.some.inj h2]
            rename_i heq _ _ _
            apply List.Mem.tail
            apply ih
            assumption
            unfold LRAT.DefaultClause.ofArray
            rw [Array.foldr_eq_foldr_data,Array.toArray_data]
            exact heq

theorem CNF.Clause.convertLRAT_sat_of_sat (clause : CNF.Clause (PosFin n)) (h : clause.convertLRAT' = some lratClause) :
    clause.eval assign → assign ⊨ lratClause := by
  intro h2
  simp only [CNF.Clause.eval, List.any_eq_true, bne_iff_ne, ne_eq] at h2
  simp only [HSat.eval, List.any_eq_true, decide_eq_true_eq]
  rcases h2 with ⟨lit, ⟨hlit1, hlit2⟩⟩
  apply Exists.intro (lit.fst, lit.snd)
  constructor
  . simp[LRAT.Clause.toList, LRAT.DefaultClause.toList]
    simp[CNF.Clause.convertLRAT'] at h
    exact CNF.Clause.mem_lrat_of_mem clause hlit1 h
  . simp_all

/--
Convert a `CNF Nat` with a certain maximum variable number into the `LRAT.DefaultFormula`
format for usage with LeanSAT.

Notably this:
1. Increments all variables as DIMACS variables start at 1 instead of 0
2. Adds a leading `none` clause. This clause *must* be persistet as the LRAT proof
   refers to the DIMACS file line by line and the DIMACS file begins with the
  `p cnf x y` meta instruction.
-/
def CNF.convertLRAT (cnf : CNF Nat) : LRAT.DefaultFormula (cnf.numLiterals + 1) :=
  let lifted := CNF.lift cnf
  let lratCnf := CNF.convertLRAT' lifted
  LRAT.DefaultFormula.ofArray (none :: lratCnf).toArray

theorem CNF.convertLRAT_readfyForRupAdd (cnf : CNF Nat) : LRAT.DefaultFormula.readyForRupAdd cnf.convertLRAT := by
  unfold CNF.convertLRAT
  apply LRAT.DefaultFormula.ofArray_readyForRupAdd

theorem CNF.convertLRAT_readfyForRatAdd (cnf : CNF Nat) : LRAT.DefaultFormula.readyForRatAdd cnf.convertLRAT := by
  unfold CNF.convertLRAT
  apply LRAT.DefaultFormula.ofArray_readyForRatAdd

theorem LRAT.unsat_of_cons_none_unsat (clauses : List (Option (LRAT.DefaultClause n))) :
    unsatisfiable (PosFin n) (LRAT.DefaultFormula.ofArray (none :: clauses).toArray)
      →
    unsatisfiable (PosFin n) (LRAT.DefaultFormula.ofArray clauses.toArray) := by
  intro h assign hassign
  apply h assign
  simp only [LRAT.Formula.formulaHSat_def, List.all_eq_true, decide_eq_true_eq] at *
  intro clause hclause
  simp_all[LRAT.DefaultFormula.ofArray, LRAT.Formula.toList, LRAT.DefaultFormula.toList]
