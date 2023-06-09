/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import Lean.Elab.Command
import LeanSAT.LRAT.Actions

open Lean Parser Elab Command

namespace LRAT

def makeDeletionArr (tokens : Array String) : Option (Array Nat) := do
  let mut encounteredError := false
  let mut deletionArr : Array Nat := #[]
  for token in tokens do
    if token == "" then continue
    match String.toNat? token with
    | some id => deletionArr := deletionArr.push id
    | none =>
      encounteredError := true
      break
  if encounteredError then none
  else some deletionArr

def makeDeletion (tokens : Array String) : Option IntAction :=
  match makeDeletionArr tokens with
  | some deletionArr => some $ .del deletionArr
  | none => none

def makeClause (clauseTokens : Array String) : Option (Array Int) := do
  let mut encounteredError := false
  let mut clause : Array Int := #[]
  for token in clauseTokens do
    if token == "" then continue
    match String.toInt? token with
    | some l => clause := clause.push l
    | none =>
      encounteredError := true
      break
  if encounteredError then none
  else some clause

def makeHints (hintTokens : Array String) : Option (Array Nat × Array (Nat × Array Nat)) := do
  if hintTokens.size == 0 then none
  else
    let mut rupHints : Array Nat := #[]
    let mut ratHints : Array (Nat × Array Nat) := #[]

    let mut encounteredError := false
    let mut processingRupHint := true
    let mut curRatHint : Option (Nat × Array Nat) := none
    for hint in hintTokens do
      match hint.toInt? with
      | some hint =>
        if hint < 0 then -- Starting a new ratHint
          if processingRupHint then
            processingRupHint := false -- Finished processingRupHint
            curRatHint := some (hint.natAbs, #[])
          else
            match curRatHint with
            | none => -- Nothing to push to ratHints because this is the first ratHint
              curRatHint := some (hint.natAbs, #[])
            | some prevRatHint =>
              ratHints := ratHints.push prevRatHint
              curRatHint := some (hint.natAbs, #[])
        else
          if processingRupHint then
            rupHints := rupHints.push hint.natAbs -- hint.natAbs = hint because hint > 0
          else
            match curRatHint with
            | some (curRatId, curRatArr) => curRatHint := (curRatId, curRatArr.push hint.natAbs)
            | none => -- This case shouldn't be possible
              encounteredError := true
              break
      | none =>
        encounteredError := true
        break
    -- Still have to add final ratHint since it is not followed by a negative number
    ratHints :=
      match curRatHint with
      | none => ratHints
      | some finalRatHint => ratHints.push finalRatHint
    if encounteredError then none
    else some (rupHints, ratHints)

def getPivot (clause : Array Int) : Literal Nat :=
  let pivotInt := clause[0]!
  if pivotInt > 0 then (pivotInt.natAbs, true)
  else (pivotInt.natAbs, false)

def makeAddition (clauseId : Nat) (clauseTokens : Array String) (hintTokens : Array String) : Option IntAction := do
  match makeClause clauseTokens, makeHints hintTokens with
  | some clause, some (rupHints, ratHints) =>
    match clause.size, ratHints.size with
    | 0, 0 => some $ .addEmpty clauseId rupHints
    | 0, _ => none -- There cannot be any ratHints for adding the empty clause because the empty clause has no pivot
    | _, 0 => some $ .addRup clauseId clause rupHints
    | _, _ => some $ .addRat clauseId clause (getPivot clause) rupHints ratHints
  | _, _ => none

/-- `lineToActionCommand` takes in a single unparsed LRAT line and attempts to parse it into an `IntAction`.
    `lineToActionCommand` will fail if the given line is not a complete unparsed LRAT line or if a syntax error
    is found in the line.

    `lineToActionCommand` is written in a `CommandElabM` monad so that it can throw errors on failure and be called
    by `loadLRATProof`-/
def lineToActionCommand (line : String) : CommandElabM IntAction := do
  let mut clauseID : Option Nat := none
  let mut firstSectionTokens : Array String := #[]
  let mut hintTokens : Array String := #[]
  let mut isDeletion : Option Bool := none -- none represents unknown
  let mut numZeroes := 0

  let line := line.replace "\t" " "
  let lineAction := (line.splitOn " ").toArray
  for token in lineAction do
    match clauseID with
    | none =>
      match String.toNat? token with
      | some id => clauseID := some id
      | none => throwError "Unable to parse id"
    | some id =>
      if firstSectionTokens == #[] && isDeletion == none then
        if token == "d" then
          isDeletion := some true
          continue -- d is not part of the clause and therefore shouldn't be added to firstSectionTokens
        else
          isDeletion := some false -- no continue because we should add token to firstSectionTokens
      if token == "0" then
        match isDeletion with
        | none => throwError "Error while loading LRAT proof"
        | some true =>
          match makeDeletion firstSectionTokens with
          | none => throwError "Error while loading LRAT proof"
          | some action => return action
        | some false =>
          if numZeroes == 0 then -- This zero ends the clause, but not the action
            numZeroes := 1
          else -- This zero ends the hint section
            match makeAddition id firstSectionTokens hintTokens with
            | none => throwError "Error while loading LRAT proof"
            | some action => return action
      else
        if numZeroes == 0 then firstSectionTokens := firstSectionTokens.push token
        else hintTokens := hintTokens.push token
  throwError "End of line should correspond with end of LRAT action"

/-- `loadLRATProof` takes in the path of an LRAT proof and attempts to output an Array of IntActions
    that correspond to the parsed LRAT proof.

    `loadLRATProof` is written as a `CommandElabM` monad so that it can be used in commands such as `loadLRAT` at
    the end of this file. -/
def loadLRATProof (path : System.FilePath) : CommandElabM (Array IntAction) := do
  let lines ← IO.FS.lines path
  let lines := lines.filter fun l => not (l.startsWith "c")
  let mut proof : Array IntAction := #[]
  for line in lines do
    proof := proof.push $ ← lineToActionCommand line
  return proof

/-- `lineToAction` takes in a single unparsed LRAT line and attempts to parse it into an `IntAction`.
    `lineToAction` will fail if the given line is not a complete unparsed LRAT line or if a syntax error
    is found in the line.

   `lineToAction` is written in an `IO` monad so that it can print errors on failure. `lineToAction` is called
   in `parseLRATProof` but can also be called independently by a program such as `main` to facilitate parsing an
   LRAT proof one line at a time and checking the LRAT proof incrementally with `incrementalLRATChecker` -/
def lineToAction (line : String) : IO (Option IntAction) := do
  let mut encounteredError := false
  let mut action : Option IntAction := none

  let mut clauseID : Option Nat := none
  let mut firstSectionTokens : Array String := #[]
  let mut hintTokens : Array String := #[]
  let mut isDeletion : Option Bool := none -- none represents unknown
  let mut numZeroes := 0

  let line := line.replace "\t" " "
  let line := line.replace "\n" ""
  let lineAction := (line.splitOn " ").toArray
  for token in lineAction do
    if action != none then
      IO.println "End of line should correspond with end of LRAT action"
      encounteredError := true
      break
    match clauseID with
    | none =>
      match String.toNat? token with
      | some id => clauseID := some id
      | none => IO.println "Unable to parse id"; encounteredError := true; break
    | some id =>
      if firstSectionTokens == #[] && isDeletion == none then
        if token == "d" then
          isDeletion := some true
          continue -- d is not part of the clause and therefore shouldn't be added to firstSectionTokens
        else
          isDeletion := some false -- no continue because we should add token to firstSectionTokens
      if token == "0" then
        match isDeletion with
        | none => IO.println "Error while loading LRAT proof"; encounteredError := true; break
        | some true =>
          match makeDeletion firstSectionTokens with
          | none => IO.println "Error while loading LRAT proof"; encounteredError := true; break
          | some curAction => action := some curAction
        | some false =>
          if numZeroes == 0 then -- This zero ends the clause, but not the action
            numZeroes := 1
          else -- This zero ends the hint section
            match makeAddition id firstSectionTokens hintTokens with
            | none =>
              IO.println "Error while loading LRAT proof"
              encounteredError := true
              break
            | some curAction => action := some curAction
      else
        if numZeroes == 0 then firstSectionTokens := firstSectionTokens.push token
        else hintTokens := hintTokens.push token
  if encounteredError then return none
  else return action

/-- `parseLRATProof` takes in the path of an LRAT proof and attempts to output an Array of IntActions
    that correspond to the parsed LRAT proof.

    `parseLRATProof` is written as an `IO` monad so that it can be used in programs such as `main`. Since the `IO` monad does
    not support `throwError` in the way that `CommandElabM` does, `parseLRATProof` returns `none` where `loadLRATProof`
    would throw an error. Other than this difference though, `loadLRATProof` and `parseLRATProof` are intended to be equivalent. -/
def parseLRATProof (path : System.FilePath) : IO (Option (Array IntAction)) := do
  let lines ← IO.FS.lines path
  let lines := lines.filter fun l => not (l.startsWith "c")
  let mut proof : Array IntAction := #[]
  let mut encounteredError := false
  for line in lines do
    match ← lineToAction line with
    | some action => proof := proof.push action
    | none => encounteredError := true
  if encounteredError then return none
  else return some proof

syntax (name := loadLRATCommand) "loadLRAT " strLit : command

@[command_elab loadLRATCommand] def elabLoadLRAT : CommandElab := fun stx => do
  match stx with
  | `(loadLRAT $file) =>
    match Syntax.isStrLit? file with
    | some file =>
        let proof ← loadLRATProof file
        IO.println s!"{proof}"
    | _ => throwError "Expected strLit: {file}"
  | _ => throwError "Failed to parse loadLRAT command"

loadLRAT "./pigeon-hole/hole6.lrat"
