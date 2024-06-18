/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.LRAT.Actions
import LeanSAT.External.Parsec

namespace LRAT

def getPivot (clause : Array Int) : Literal Nat :=
  let pivotInt := clause[0]!
  if pivotInt > 0 then (pivotInt.natAbs, true)
  else (pivotInt.natAbs, false)

namespace Parser

/-
This implements a (correct) version of the grammar presented in:
https://www.cs.cmu.edu/~mheule/publications/lrat.pdf
-/

open Parsec Byte

@[inline]
def parsePos : Parsec ByteArray.Iterator Nat := do
  let ident ← Byte.digits
  if ident == 0 then
    fail "id was 0"
  else
    return ident

@[inline]
def parseNeg : Parsec ByteArray.Iterator  Int := do
  skipChar '-'
  let nat ← parsePos
  return -nat

@[inline]
def parseId : Parsec ByteArray.Iterator Nat := parsePos

@[inline]
def parseZero : Parsec ByteArray.Iterator Unit := skipChar '0'

def parseIdList : Parsec ByteArray.Iterator (Array Nat) := do
  many idWs
where
  @[inline]
  idWs : Parsec ByteArray.Iterator Nat := do
    let ident ← attempt parseId
    skipChar ' '
    return ident

def parseDelete (_ident : Nat) : Parsec ByteArray.Iterator IntAction := do
  skipChar 'd'
  skipChar ' '
  let idList ← parseIdList
  parseZero
  return .del idList

def parseLit : Parsec ByteArray.Iterator Int := do
  parseNeg <|> (Int.ofNat <$> parsePos)

def parseClause : Parsec ByteArray.Iterator (Array Int) := do
  let lits ← many litWs
  parseZero
  return lits
where
  @[inline]
  litWs : Parsec ByteArray.Iterator Int := do
    let lit ← attempt parseLit
    skipChar ' '
    return lit

def parseRes : Parsec ByteArray.Iterator (Nat × Array Nat) := do
  let lhs ← parseNeg
  skipChar ' '
  let idents ← parseIdList
  return (lhs.natAbs, idents)

def parseRat (ident : Nat) : Parsec ByteArray.Iterator IntAction := do
  let clause ← parseClause
  skipChar ' '
  let rupHints ← parseIdList
  let ratHints ← many (attempt parseRes)
  parseZero
  match clause.size, ratHints.size with
  | 0, 0 => return .addEmpty ident rupHints
  | 0, _ => fail "There cannot be any ratHints for adding the empty clause"
  | _, 0 => return .addRup ident clause rupHints
  | _, _ => return .addRat ident clause (getPivot clause) rupHints ratHints

def parseLine : Parsec ByteArray.Iterator IntAction := do
  let ident ← parseId
  skipChar ' '
  parseDelete ident <|> parseRat ident

partial def parseLines : Parsec ByteArray.Iterator (Array IntAction) :=
  go #[]
where
  go (actions : Array IntAction) : Parsec ByteArray.Iterator (Array IntAction) := do
    if (← peek!) == 'c'.toNat.toUInt8 then
      let _ ← many (satisfy (· != '\n'.toNat.toUInt8))
      skipChar '\n'
      if ← eof? then
        pure actions
      else
        go actions
    else
      let action ← parseLine
      skipChar '\n'
      let actions := actions.push action
      if ← eof? then
        pure actions
      else
        go actions

end Parser

/--
A quicker version of `IO.FS.readFile` for big files. Note that this assumes the file contains valid
UTF-8. As we only use this to parse trusted input from a SAT solver this is fine.
-/
def readFileQuick (path : System.FilePath) : IO ByteArray := do
  let mdata ← path.metadata
  let handle ← IO.FS.Handle.mk path .read
  handle.read mdata.byteSize.toUSize

def loadLRATProof (path : System.FilePath) : IO (Array IntAction) := do
  let proof ← readFileQuick path
  match Parser.parseLines.run <| .fresh proof with
  | .ok actions => return actions
  | .error err => throw <| .userError err

def parseLRATProof (proof : ByteArray) : Option (Array IntAction) :=
  match Parser.parseLines.run <| .fresh proof with
  | .ok actions => some actions
  | .error .. => none

def dumpLRATProof (path : System.FilePath) (proof : Array IntAction) : IO Unit := do
  let out := proof.foldl (init := "") (· ++ serialize · ++ "\n")
  IO.FS.writeFile path out
where
  serialize (a : IntAction) : String :=
    match a with
    | .addEmpty id hints =>
      s!"{id} 0 {serializeIdList hints}0"
    | .addRup id c hints =>
      s!"{id} {serializeClause c}0 {serializeIdList hints}0"
    | .addRat id c _ rupHints ratHints =>
      s!"{id} {serializeClause c}0 {serializeIdList rupHints}0 {serializeRatHints ratHints}0"
    | .del ids =>
      -- TODO: 1 is not an actual id
      s!"1 d{serializeIdList ids}0"

  serializeIdList (ids : Array Nat) : String :=
    ids.foldl (init := "") (· ++ s!"{·} ")

  serializeClause (clause : Array Int) : String :=
    clause.foldl (init := "") (· ++ s!"{·} ")

  serializeRatHint (hint : Nat × Array Nat) : String :=
    s!"-{hint.fst} {serializeIdList hint.snd}"

  serializeRatHints (hints : Array (Nat × Array Nat)) : String :=
    hints.foldl (init := "") (· ++ serializeRatHint ·)

end LRAT
