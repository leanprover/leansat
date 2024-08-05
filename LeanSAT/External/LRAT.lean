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

open Parsec ByteArray

namespace Text
/-
This implements a (corrected) version of the grammar presented in:
https://www.cs.cmu.edu/~mheule/publications/lrat.pdf
-/


@[inline]
def parsePos : Parser Nat := do
  let ident ← digits
  if ident == 0 then
    fail "id was 0"
  else
    return ident

@[inline]
def parseNeg : Parser Int := do
  skipByteChar '-'
  let nat ← parsePos
  return -nat

@[inline]
def parseId : Parser Nat := parsePos

@[inline]
def parseZero : Parser Unit := skipByteChar '0'

def parseIdList : Parser (Array Nat) := do
  many idWs
where
  @[inline]
  idWs : Parser Nat := do
    let ident ← attempt parseId
    skipByteChar ' '
    return ident

def parseDelete : Parser IntAction := do
  skipByteChar 'd'
  skipByteChar ' '
  let idList ← parseIdList
  parseZero
  return .del idList

def parseLit : Parser Int := do
  if (← peek!) == '-'.toUInt8 then
    parseNeg
  else
    Int.ofNat <$> parsePos

def parseClause : Parser (Array Int) := do
  let lits ← many litWs
  parseZero
  return lits
where
  @[inline]
  litWs : Parser Int := do
    let lit ← attempt parseLit
    skipByteChar ' '
    return lit

def parseRes : Parser (Nat × Array Nat) := do
  let lhs ← parseNeg
  skipByteChar ' '
  let idents ← parseIdList
  return (lhs.natAbs, idents)

def parseRat (ident : Nat) : Parser IntAction := do
  let clause ← parseClause
  skipByteChar ' '
  let rupHints ← parseIdList
  let ratHints ← many (attempt parseRes)
  parseZero
  match clause.size, ratHints.size with
  | 0, 0 => return .addEmpty ident rupHints
  | 0, _ => fail "There cannot be any ratHints for adding the empty clause"
  | _, 0 => return .addRup ident clause rupHints
  | _, _ => return .addRat ident clause (getPivot clause) rupHints ratHints

def parseAction : Parser IntAction := do
  let ident ← parseId
  skipByteChar ' '
  if (← peek!) == 'd'.toUInt8 then
    parseDelete
  else
    parseRat ident

partial def parseActions : Parser (Array IntAction) :=
  go #[]
where
  go (actions : Array IntAction) : Parser (Array IntAction) := do
    if (← peek!) == 'c'.toUInt8 then
      let _ ← many (satisfy (· != '\n'.toUInt8))
      skipByteChar '\n'
      if ← eof? then
        pure actions
      else
        go actions
    else
      let action ← parseAction
      skipByteChar '\n'
      let actions := actions.push action
      if ← eof? then
        return actions
      else
        go actions

end Text

namespace Binary

@[inline]
def parseZero : Parser Unit := skipByte 0

-- see: https://github.com/marijnheule/drat-trim?tab=readme-ov-file#binary-drat-format
-- see: https://github.com/arminbiere/lrat-trim/blob/80f22c57fb2d74cb72210f5b334a1ffe2160a628/lrat-trim.c#L1579-L1595
partial def parseLit : Parser Int := do
  go 0 0
where
  go (uidx : UInt64) (shift : UInt64) : Parser Int := do
    let uch ← any
    if shift == 28 && ((uch &&& ~~~15) != 0) then
      fail "Excessive literal"
    else if uch == 0 then
        fail "Invalid zero byte in literal"
    else
      let uidx := uidx ||| ((uch &&& 127).toUInt64 <<< shift)
      if uch &&& 128 == 0 then
        let idx := uidx >>> 1
        if (1 &&& uidx) != 0 then
          return (-(idx).toNat : Int)
        else
          return (idx.toNat : Int)
      else
        go uidx (shift + 7)

@[inline]
def parseNeg : Parser Nat := do
  let lit ← parseLit
  if lit < 0 then
    return lit.natAbs
  else
    fail "parsed non negative lit where negative was expected"

@[inline]
def parsePos : Parser Nat := do
  let lit ← parseLit
  if lit > 0 then
    return lit.natAbs
  else
    fail "parsed non positive lit where positive was expected"

@[inline]
def parseId : Parser Nat := parsePos

@[specialize]
partial def manyTillZero (parser : Parser α) : Parser (Array α) :=
  go #[]
where
  @[specialize]
  go (acc : Array α) : Parser (Array α) := do
    if (← peek!) == 0 then
      return acc
    else
      let elem ← parser
      go <| acc.push elem

@[specialize]
partial def manyTillNegOrZero (parser : Parser α) : Parser (Array α) :=
  go #[]
where
  @[specialize]
  go (acc : Array α) : Parser (Array α) := do
    let byte ← peek!
    if (1 &&& byte != 0) || byte == 0 then
      return acc
    else
      let elem ← parser
      go <| acc.push elem

@[inline]
def parseIdList : Parser (Array Nat) :=
  manyTillNegOrZero parseId

@[inline]
def parseClause : Parser (Array Int) := do
  manyTillZero parseLit

def parseRes : Parser (Nat × Array Nat) := do
  let lhs ← parseNeg
  let idents ← parseIdList
  return (lhs, idents)

@[inline]
def parseRatHints : Parser (Array (Nat × Array Nat)) := do
  manyTillZero parseRes

def parseAction : Parser IntAction := do
  let discr ← any
  if discr == 'a'.toUInt8 then
    parseAdd
  else if discr == 'd'.toUInt8 then
    parseDelete
  else
    fail s!"Expected a or d got: {discr}"
where
  parseAdd : Parser IntAction := do
    let ident ← parseId
    let clause ← parseClause
    parseZero
    let rupHints ← parseIdList
    let ratHints ← parseRatHints
    parseZero
    match clause.size, ratHints.size with
    | 0, 0 => return .addEmpty ident rupHints
    | 0, _ => fail "There cannot be any ratHints for adding the empty clause"
    | _, 0 => return .addRup ident clause rupHints
    | _, _ => return .addRat ident clause (getPivot clause) rupHints ratHints

  parseDelete : Parser IntAction := do
    let idList ← parseIdList
    parseZero
    return .del idList

partial def parseActions : Parser (Array IntAction) := do
  go #[]
where
  go (actions : Array IntAction) : Parser (Array IntAction) := do
    let action ← parseAction
    let actions := actions.push action
    if ← eof? then
      return actions
    else
      go actions

end Binary

/--
Based on the byte parses the input either as a binary or a clear text LRAT.
-/
def parseActions : Parser (Array IntAction) := do
  let byte ← peek!
  if byte == 'a'.toUInt8 || byte == 'd'.toUInt8 then
    Binary.parseActions
  else
    Text.parseActions

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
  match Parser.parseActions.run proof with
  | .ok actions => return actions
  | .error err => throw <| .userError err

def parseLRATProof (proof : ByteArray) : Option (Array IntAction) :=
  match Parser.parseActions.run proof with
  | .ok actions => some actions
  | .error .. => none

def lratProofToString (proof : Array IntAction) : String :=
  proof.foldl (init := "") (· ++ serialize · ++ "\n")
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
      -- Note: 1 is not an actual id but our parser ignores identies on d anyways.
      s!"1 d {serializeIdList ids}0"

  serializeIdList (ids : Array Nat) : String :=
    ids.foldl (init := "") (· ++ s!"{·} ")

  serializeClause (clause : Array Int) : String :=
    clause.foldl (init := "") (· ++ s!"{·} ")

  serializeRatHint (hint : Nat × Array Nat) : String :=
    s!"-{hint.fst} {serializeIdList hint.snd}"

  serializeRatHints (hints : Array (Nat × Array Nat)) : String :=
    hints.foldl (init := "") (· ++ serializeRatHint ·)

def dumpLRATProof (path : System.FilePath) (proof : Array IntAction) : IO Unit := do
  let out := lratProofToString proof
  IO.FS.writeFile path out

end LRAT
