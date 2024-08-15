/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.LRAT.Actions
import LeanSAT.LRAT.Internal.Convert
import LeanSAT.LRAT.Internal.LRATChecker
import LeanSAT.LRAT.Internal.LRATCheckerSound
import Std.Sat.CNF

open Std.Sat

namespace LeanSAT
namespace LRAT

def verify (lratProof : Array IntAction) (cnf : CNF Nat) : Bool :=
  let internalFormula := CNF.convertLRAT cnf
  let lratProof := lratProof.toList
  let lratProof := lratProof.map (LRAT.intActionToDefaultClauseAction _)
  let lratProof : List { act // LRAT.WellFormedAction act } :=
    lratProof.filterMap
      (fun actOpt =>
        match actOpt with
        | none => none
        | some (LRAT.Action.addEmpty id rupHints) =>
          some ⟨LRAT.Action.addEmpty id rupHints, by simp only [LRAT.WellFormedAction]⟩
        | some (LRAT.Action.addRup id c rupHints) =>
          some ⟨LRAT.Action.addRup id c rupHints, by simp only [LRAT.WellFormedAction]⟩
        | some (LRAT.Action.del ids) =>
          some ⟨LRAT.Action.del ids, by simp only [LRAT.WellFormedAction]⟩
        | some (LRAT.Action.addRat id c pivot rupHints ratHints) =>
          if h : pivot ∈ LRAT.Clause.toList c then
            some ⟨
              LRAT.Action.addRat id c pivot rupHints ratHints,
              by simp [LRAT.WellFormedAction, LRAT.Clause.limplies_iff_mem, h]
            ⟩
          else
            -- TODO: report this
            none
      )
  let lratProof := lratProof.map Subtype.val
  let checkerResult := LRAT.lratChecker internalFormula lratProof
  checkerResult = .success

theorem verify_sound (proof : Array IntAction) (cnf : CNF Nat) : verify proof cnf → cnf.Unsat := by
  intro h1
  unfold verify at h1
  simp only [decide_eq_true_eq] at h1
  have h2 :=
    lratCheckerSound
      _
      (by apply CNF.convertLRAT_readfyForRupAdd)
      (by apply CNF.convertLRAT_readfyForRatAdd)
      _
      (by
        intro action h
        simp only [List.mem_map, List.mem_filterMap] at h
        rcases h with ⟨WellFormedActions, _, h2⟩
        rw [← h2]
        exact WellFormedActions.property)
      h1
  apply CNF.unsat_of_convertLRAT_unsat
  assumption

end LRAT
end LeanSAT
