/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.LRAT.Formula.RatAddSound

namespace LRAT
namespace DefaultFormula

instance {n : Nat} : Formula (PosFin n) (DefaultClause n) (DefaultFormula n) where
  toList := toList
  readyForRupAdd := readyForRupAdd
  readyForRatAdd := readyForRatAdd
  ofArray := ofArray
  ofArray_readyForRupAdd := ofArray_readyForRupAdd
  ofArray_readyForRatAdd := ofArray_readyForRatAdd
  insert := insert
  insert_iff := insert_iff
  insert_readyForRupAdd := insert_readyForRupAdd
  insert_readyForRatAdd := insert_readyForRatAdd
  delete := delete
  delete_readyForRupAdd := delete_readyForRupAdd
  delete_readyForRatAdd := delete_readyForRatAdd
  delete_subset := delete_subset
  formulaHSat_def := formulaHSat_def
  performRupAdd := performRupAdd
  rupAdd_result := rupAdd_result
  rupAdd_sound := rupAdd_sound
  performRatAdd := performRatAdd
  ratAdd_result := ratAdd_result
  ratAdd_sound := ratAdd_sound
  dimacs := dimacs
  dbg_info := dbg_info
