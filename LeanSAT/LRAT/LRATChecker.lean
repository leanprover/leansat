/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.External.LRAT
import LeanSAT.LRAT.Formula.Instance

namespace LRAT

inductive Result
  | success
  | out_of_proof
  | rup_failure
deriving Inhabited, DecidableEq, BEq

instance : ToString Result where
  toString := fun
    | Result.success => "success"
    | Result.out_of_proof => "out of proof"
    | Result.rup_failure => "rup failure"

instance : LawfulBEq Result where
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> first | rfl | cases h
  rfl := by
    intro a
    cases a <;> decide

open List Clause Formula Result Action Formula Literal

def incrementalLRATChecker [DecidableEq α] [Clause α β] [HSat α σ] [Formula α β σ] (f : σ) (action : Action β α) : σ × Result :=
  match action with
  | addEmpty _ rupHints =>
    let (f, checkSuccess) := performRupAdd f empty rupHints
    if checkSuccess then (f, success)
    else (f, rup_failure)
  | addRup _ c rupHints =>
    let (f, checkSuccess) := performRupAdd f c rupHints
    if checkSuccess then (f, out_of_proof)
    else (f, rup_failure)
  | addRat _ c pivot rupHints ratHints =>
    let (f, checkSuccess) := performRatAdd f c pivot rupHints ratHints
    if checkSuccess then (f, out_of_proof)
    else (f, rup_failure)
  | del ids => (delete f ids, out_of_proof)

def lratChecker [DecidableEq α] [Clause α β] [HSat α σ] [Formula α β σ] (f : σ) (prf : List (Action β α)) : Result :=
  match prf with
  | nil => out_of_proof
  | addEmpty _ rupHints :: _ =>
    let (_, checkSuccess) := performRupAdd f empty rupHints
    if checkSuccess then success
    else rup_failure
  | addRup _ c rupHints :: restPrf =>
    let (f, checkSuccess) := performRupAdd f c rupHints
    if checkSuccess then lratChecker f restPrf
    else rup_failure
  | addRat _ c pivot rupHints ratHints :: restPrf =>
    let (f, checkSuccess) := performRatAdd f c pivot rupHints ratHints
    if checkSuccess then lratChecker f restPrf
    else rup_failure
  | del ids :: restPrf => lratChecker (delete f ids) restPrf
