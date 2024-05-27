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

open Lean Elab Command in
/-- `loadLRATProof` takes in the path of an LRAT proof and attempts to output an Array of IntActions
    that correspond to the parsed LRAT proof.

    `loadLRATProof` is written as a `CommandElabM` monad so that it can be used in commands such as `loadLRAT` at
    the end of this file. -/
def loadLRATProof (path : System.FilePath) : CommandElabM (Array IntAction) := do
  let proof ← IO.FS.readBinFile path
  match Parser.parseLines.run <| .fresh proof with
  | .ok actions => return actions
  | .error err => throwError err

def parseLRATProof (proof : ByteArray) : Option (Array IntAction) := Id.run do
  match Parser.parseLines.run <| .fresh proof with
  | .ok actions => return some actions
  | .error .. => return none

/-- `readLRATProof` takes in the path of an LRAT proof and attempts to output an Array of IntActions
    that correspond to the parsed LRAT proof. -/
def readLRATProof (path : System.FilePath) : IO (Option (Array IntAction)) := do
  let proof ← IO.FS.readBinFile path
  match Parser.parseLines.run <| .fresh proof with
  | .ok actions => return some actions
  | .error .. => return none
