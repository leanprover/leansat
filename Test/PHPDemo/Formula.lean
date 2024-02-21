/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.External.Solver
import LeanSAT.LRAT.LRATChecker
import LeanSAT.LRAT.LRATCheckerSound
import LeanSAT.External.LRAT

open Dimacs LRAT DefaultClause DefaultFormula Result Lean Classical Action

-- Defining the variables
def v1 : PosFin 13 := ⟨1, by simp⟩ -- p1 in h1
def v2 : PosFin 13 := ⟨2, by simp⟩ -- p1 in h2
def v3 : PosFin 13 := ⟨3, by simp⟩ -- p1 in h3
def v4 : PosFin 13 := ⟨4, by simp⟩ -- p2 in h1
def v5 : PosFin 13 := ⟨5, by simp⟩ -- p2 in h2
def v6 : PosFin 13 := ⟨6, by simp⟩ -- p2 in h3
def v7 : PosFin 13 := ⟨7, by simp⟩ -- p3 in h1
def v8 : PosFin 13 := ⟨8, by simp⟩ -- p3 in h2
def v9 : PosFin 13 := ⟨9, by simp⟩ -- p3 in h3
def v10 : PosFin 13 := ⟨10, by simp⟩ -- p4 in h1
def v11 : PosFin 13 := ⟨11, by simp⟩ -- p4 in h2
def v12 : PosFin 13 := ⟨12, by simp⟩ -- p4 in h3
-- Clauses indicating that each pigeon must go in some hole
def c1 := ofArray #[(v1, true), (v2, true), (v3, true)]
def c2 := ofArray #[(v4, true), (v5, true), (v6, true)]
def c3 := ofArray #[(v7, true), (v8, true), (v9, true)]
def c4 := ofArray #[(v10, true), (v11, true), (v12, true)]
-- Clauses indicating at most one pigeon must go in hole 1
def c5 := ofArray #[(v1, false), (v4, false)]
def c6 := ofArray #[(v1, false), (v7, false)]
def c7 := ofArray #[(v1, false), (v10, false)]
def c8 := ofArray #[(v4, false), (v7, false)]
def c9 := ofArray #[(v4, false), (v10, false)]
def c10 := ofArray #[(v7, false), (v10, false)]
-- Clauses indicating at most one pigeon must go in hole 2
def c11 := ofArray #[(v2, false), (v5, false)]
def c12 := ofArray #[(v2, false), (v8, false)]
def c13 := ofArray #[(v2, false), (v11, false)]
def c14 := ofArray #[(v5, false), (v8, false)]
def c15 := ofArray #[(v5, false), (v11, false)]
def c16 := ofArray #[(v8, false), (v11, false)]
-- Clauses indicating at most one pigeon must go in hole 3
def c17 := ofArray #[(v3, false), (v6, false)]
def c18 := ofArray #[(v3, false), (v9, false)]
def c19 := ofArray #[(v3, false), (v12, false)]
def c20 := ofArray #[(v6, false), (v9, false)]
def c21 := ofArray #[(v6, false), (v12, false)]
def c22 := ofArray #[(v9, false), (v12, false)]

def php3_formula : DefaultFormula 13 :=
  DefaultFormula.ofArray #[none, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22]

def load_php3_lrat_proof : IO (List ({act : DefaultClauseAction 13 // wellFormedAction act})) := do
  let cnfPath : System.FilePath := "." / "Test" / "PHPDemo" / "php3.cnf"
  let lratPath : System.FilePath := "." / "Test" / "PHPDemo" / "php3.lrat"
  IO.FS.writeFile cnfPath $ dimacs php3_formula
  let _ ← satQuery cnfPath.toString lratPath.toString
  match ← parseLRATProof lratPath.toString with
  | some lratProof =>
    let lratProof ← lratProof.mapM (intActionToDefaultClauseActionIO 13)
    let lratProof :=
      lratProof.filterMap
        (fun actOpt =>
          match actOpt with
          | none => none
          | some (addEmpty id rupHints) =>
            have isWellFormed : wellFormedAction (addEmpty id rupHints) := by simp only [wellFormedAction]
            some ⟨addEmpty id rupHints, isWellFormed⟩
          | some (addRup id c rupHints) =>
            have isWellFormed : wellFormedAction (addRup id c rupHints) := by simp only [wellFormedAction]
            some ⟨addRup id c rupHints, isWellFormed⟩
          | some (del ids) =>
            have isWellFormed : wellFormedAction (del ids) := by simp only [wellFormedAction]
            some ⟨del ids, isWellFormed⟩
          | some (addRat id c pivot rupHints ratHints) =>
            none -- I don't need to deal with this for php3 because the php3 proof doesn't include any ratAdds
        )
    pure lratProof.toList
  | none => pure [] -- Failure

initialize certified_php3_lrat_proof : List ({act : DefaultClauseAction 13 // wellFormedAction act}) ← load_php3_lrat_proof
