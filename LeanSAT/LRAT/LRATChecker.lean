/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.LRAT.Actions
import LeanSAT.LRAT.Internal.Formula.Instance

open Sat

namespace LRAT

inductive Result
  | success
  | outOfProof
  | rupFailure
deriving Inhabited, DecidableEq, BEq

instance : ToString Result where
  toString := fun
    | .success => "success"
    | .outOfProof => "out of proof"
    | .rupFailure => "rup failure"

instance : LawfulBEq Result where
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> first | rfl | cases h
  rfl := by
    intro a
    cases a <;> decide

open Formula

def incrementalLRATChecker [DecidableEq α] [Clause α β] [HSat α σ] [Formula α β σ] (f : σ)
    (action : Action β α) :
    σ × Result :=
  match action with
  | .addEmpty _ rupHints =>
    let (f, checkSuccess) := performRupAdd f Clause.empty rupHints
    if checkSuccess then (f, .success)
    else (f, .rupFailure)
  | .addRup _ c rupHints =>
    let (f, checkSuccess) := performRupAdd f c rupHints
    if checkSuccess then (f, .outOfProof)
    else (f, .rupFailure)
  | .addRat _ c pivot rupHints ratHints =>
    let (f, checkSuccess) := performRatAdd f c pivot rupHints ratHints
    if checkSuccess then (f, .outOfProof)
    else (f, .rupFailure)
  | .del ids => (delete f ids, .outOfProof)

def lratChecker [DecidableEq α] [Clause α β] [HSat α σ] [Formula α β σ] (f : σ)
    (prf : List (Action β α)) :
    Result :=
  match prf with
  | [] => .outOfProof
  | .addEmpty _ rupHints :: _ =>
    let (_, checkSuccess) := performRupAdd f Clause.empty rupHints
    if checkSuccess then .success
    else .rupFailure
  | .addRup _ c rupHints :: restPrf =>
    let (f, checkSuccess) := performRupAdd f c rupHints
    if checkSuccess then lratChecker f restPrf
    else .rupFailure
  | .addRat _ c pivot rupHints ratHints :: restPrf =>
    let (f, checkSuccess) := performRatAdd f c pivot rupHints ratHints
    if checkSuccess then lratChecker f restPrf
    else .rupFailure
  | .del ids :: restPrf => lratChecker (delete f ids) restPrf
