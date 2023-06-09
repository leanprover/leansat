/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.Sat.Literal
import LeanSAT.External.DimacsLRAT
import LeanSAT.LRAT.Clause

namespace LRAT

/-- β is for the type of a clause, α is for the type of variables -/
inductive Action (β : (Type v)) (α : (Type w))
  | addEmpty (id : Nat) (rupHints : Array Nat)
  | addRup (id : Nat) (c : β) (rupHints : Array Nat)
  | addRat (id : Nat) (c : β) (pivot : Literal α) (rupHints : Array Nat) (ratHints : Array (Nat × Array (Nat)))
  | del (ids : Array Nat)
deriving Inhabited, BEq, Repr

def Action.toString [ToString β] [ToString α] : Action β α → String
  | .addEmpty id rup => s!"addEmpty (id: {id}) (hints: {rup})"
  | .addRup id c rup => s!"addRup {c} (id : {id}) (hints: {rup})"
  | .addRat id c l rup rat => s!"addRat {c} (id: {id}) (pivot: {l}) (rup hints: {rup}) (rat hints: {rat})"
  | .del ids => s!"del {ids}"

instance [ToString β] [ToString α] : ToString (Action β α) := ⟨Action.toString⟩

open Action

/-- Action where variables are (positive) nats, clauses are arrays of ints, and ids are nats. This Action type is meant to be a
    convenient target for parsing LRAT proofs. -/
abbrev IntAction := Action (Array Int) Nat

/-- Action where variables have type PosFin n, clauses are default clauses, and ids are nats. This Action type is meant to be
    usable for verifying LRAT proofs that operate on default formulas. -/
abbrev DefaultClauseAction (n : Nat) := Action (DefaultClause n) (PosFin n)

/-- A predicate for Actions that ensures that the pivot of a clause is always included in the clause. In the LRAT format, the
    clause's pivot is always its first literal. However, from an interface perspective, it is awkward to require that all `Clause`
    implementations preserve the ordering of their literals. It is also awkward to have the pivot in the `addRat` action not included
    in the clause itself, since then the pivot would need to be readded to the clause when it is added to the formula. So to avoid
    imposing awkward constraints on the `Clause` interface, and to avoid requiring `Formula` implementations to add pivots to the clauses
    provided by the `addRat` action, we use this predicate to indicate that the pivot provided by the `addRat` action is indeed in the
    provided clause. -/
def wellFormedAction [Clause α β] : Action β α → Prop
  | addRat _ c p _ _ => Sat.limplies α p c -- Note that `Sat.limplies α p c` is equivalent to `p ∈ toList c` by `limplies_iff_mem` in CNF.lean
  | _ => True

def natLiteralToPosFinLiteralIO {n : Nat} (x : Literal Nat) (x_ne_zero : x.1 ≠ 0) : IO (Option (Literal (PosFin n))) := do
  if h : x.1 < n then
    return some (⟨x.1, ⟨Nat.zero_lt_of_ne_zero x_ne_zero, h⟩⟩, x.2)
  else
    IO.println s!"Given literal {x} is outside of the bounds specified by the number of variables"
    return none

/-- Since `IntAction` is a convenient parsing target and `DefaultClauseAction` is a useful Action type for working with default
    clauses, an expected workflow pattern is to parse an external LRAT proof into a list of `IntAction`s, and then use this function
    to convert that list of `IntAction`s to `DefaultClauseAction`s.

    This function returns an `Option` type so that `none` can be returned if converting from the `IntAction` to `DefaultClauseAction`
    fails. This can occur if any of the literals in the `IntAction` are 0 or ≥ n. -/
def intActionToDefaultClauseActionIO (n : Nat) : IntAction → IO (Option (DefaultClauseAction n))
  | addEmpty cId rupHints => return some $ addEmpty cId rupHints
  | addRup cId c rupHints => do
    let c : Array (Option (Literal (PosFin n))) ←
      c.mapM (fun x => if h : x ≠ 0 then Dimacs.intToLiteralIO x h else return none)
    if c.contains none then
      IO.println s!"Failed to convert at least one literal in {c}"
      return none
    else
      let c := c.filterMap id
      match Clause.ofArray c with
      | none => IO.println s!"Clause {c} contains complementary literals"; return none
      | some c => return some $ addRup cId c rupHints
  | addRat cId c pivot rupHints ratHints => do
    if h : pivot.1 ≠ 0 then
      let some pivot ← natLiteralToPosFinLiteralIO pivot h
        | IO.println s!"Failed to turn {pivot} to a literal"; return none
      let c : Array (Option (Literal (PosFin n))) ←
        c.mapM (fun x => if h : x ≠ 0 then Dimacs.intToLiteralIO x h else return none)
      if c.contains none then
        IO.println s!"Failed to convert at least one literal in {c}"
        return none
      else
        let c := c.filterMap id
        match Clause.ofArray c with
        | none => IO.println s!"Clause {c} contains complementary literals"; return none
        | some c => return some $ addRat cId c pivot rupHints ratHints
    else
      return none
  | del ids => return some $ del ids

open Lean Parser Elab Command

/-- Since `IntAction` is a convenient parsing target and `DefaultClauseAction` is a useful Action type for working with default
    clauses, an expected workflow pattern is to parse an external LRAT proof into a list of `IntAction`s, and then use this function
    to convert that list of `IntAction`s to `DefaultClauseAction`s.

    This function throws an error if any of the literals in the `IntAction` are 0 or ≥ n. -/
def intActionToDefaultClauseAction (n : Nat) : IntAction → CommandElabM (DefaultClauseAction n)
  | addEmpty cId rupHints => return addEmpty cId rupHints
  | addRup cId c rupHints => do
    let c : Array (Option (Literal (PosFin n))) ←
      c.mapM (fun x => if h : x ≠ 0 then Dimacs.intToLiteralIO x h else throwError "Parsing error")
    if c.contains none then
      throwError "Failed to convert at least one literal in {c}"
    else
      let c := c.filterMap id
      match Clause.ofArray c with
      | none => throwError "Clause {c} contains complementary literals"
      | some c => return addRup cId c rupHints
  | addRat cId c pivot rupHints ratHints => do
    if h : pivot.1 ≠ 0 then
      let some pivot ← natLiteralToPosFinLiteralIO pivot h
        | throwError "Failed to turn {pivot} to a literal"
      let c : Array (Option (Literal (PosFin n))) ←
        c.mapM (fun x => if h : x ≠ 0 then Dimacs.intToLiteralIO x h else throwError "Parsing error")
      if c.contains none then
        throwError "Failed to convert at least one literal in {c}"
      else
        let c := c.filterMap id
        match Clause.ofArray c with
        | none => throwError "Clause {c} contains complementary literals"
        | some c => return addRat cId c pivot rupHints ratHints
    else
      throwError "pivot cannot be 0"
  | del ids => return del ids
