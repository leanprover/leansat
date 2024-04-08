/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import Lean.Elab.Command
import LeanSAT.LRAT.Actions

open Lean Elab Command

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

open Parsec

@[inline]
def tryCatch (p : Parsec α)
    (csuccess : α → Parsec β)
    (cerror : Unit → Parsec β)
    : Parsec β := fun it =>
  match p it with
  | .success rem a => csuccess a rem
  | .error rem err =>
    -- We assume that it.s never changes as the `Parsec` monad only modifies `it.pos`.
    if it.pos = rem.pos then cerror () rem else .error rem err

-- TODO: upstream, linearity bug in manyCore orig impl
@[specialize]
partial def manyCore (p : Parsec α) (acc : Array α) : Parsec $ Array α :=
  tryCatch p (manyCore p <| acc.push ·) (fun _ => pure acc)

-- TODO: delete after manyCore upstream
@[inline]
def many (p : Parsec α) : Parsec $ Array α := manyCore p #[]

-- TODO: delete after manyCore upstream
@[inline]
def many1 (p : Parsec α) : Parsec $ Array α := do manyCore p #[←p]

/--
Assumes `c` is between `0` and `9`
-/
def digitToNat (c : Char) : Nat := c.toNat - '0'.toNat

def digitsToNat (digits : Array Nat) : Nat :=
  digits.foldl (fun r d => r * 10 + d) 0

def parsePos : Parsec Nat := do
  let digits ← many1 (digitToNat <$> digit)
  let ident := digitsToNat digits
  if ident == 0 then
    fail "id was 0"
  else
    return ident

def parseNeg : Parsec Int := do
  skipChar '-'
  let nat ← parsePos
  return -nat

def parseId : Parsec Nat := parsePos

def parseZero : Parsec Unit := skipChar '0'

def parseIdList : Parsec (Array Nat) := do
  many idWs
where
  idWs : Parsec Nat := do
    let ident ← attempt parseId
    ws
    return ident

def parseDelete (_ident : Nat) : Parsec IntAction := do
  skipChar 'd'
  ws
  let idList ← parseIdList
  parseZero
  return .del idList

def parseLit : Parsec Int := do
  parseNeg <|> (Int.ofNat <$> parsePos)

def parseClause : Parsec (Array Int) := do
  let lits ← many litWs
  parseZero
  return lits
where
  litWs : Parsec Int := do
    let lit ← attempt parseLit
    ws
    return lit

def parseRes : Parsec (Nat × Array Nat) := do
  let lhs ← parseNeg
  ws
  let idents ← parseIdList
  return (lhs.natAbs, idents)

def parseRat (ident : Nat) : Parsec IntAction := do
  let clause ← parseClause
  ws
  let rupHints ← parseIdList
  let ratHints ← many (attempt parseRes)
  parseZero
  match clause.size, ratHints.size with
  | 0, 0 => return .addEmpty ident rupHints
  | 0, _ => fail "There cannot be any ratHints for adding the empty clause"
  | _, 0 => return .addRup ident clause rupHints
  | _, _ => return .addRat ident clause (getPivot clause) rupHints ratHints

def parseLine : Parsec IntAction := do
  let ident ← parseId
  ws
  parseDelete ident <|> parseRat ident

partial def parseLines : Parsec (Array IntAction) :=
  go #[]
where
  go (actions : Array IntAction) : Parsec (Array IntAction) := do
    let actions ←
      if (← peek!) == 'c' then
        let _ ← many (satisfy (· != '\n'))
        skipChar '\n'
        pure actions
      else
        let action ← parseLine
        skipChar '\n'
        pure (actions.push action)
    (eof *> pure actions) <|> go actions

end Parser

/-- `loadLRATProof` takes in the path of an LRAT proof and attempts to output an Array of IntActions
    that correspond to the parsed LRAT proof.

    `loadLRATProof` is written as a `CommandElabM` monad so that it can be used in commands such as `loadLRAT` at
    the end of this file. -/
def loadLRATProof (path : System.FilePath) : CommandElabM (Array IntAction) := do
  let proof ← IO.FS.readFile path
  match Parser.parseLines |>.run proof with
  | .ok actions => return actions
  | .error err => throwError err

def lineToAction (line : String) : Option IntAction :=
  match Parser.parseLine |>.run line.trim with
  | .ok action => some action
  | .error .. => none

def parseLRATProof (proof : String) : Option (Array IntAction) := Id.run do
  match Parser.parseLines |>.run proof with
  | .ok actions => return some actions
  | .error .. => return none

/-- `readLRATProof` takes in the path of an LRAT proof and attempts to output an Array of IntActions
    that correspond to the parsed LRAT proof. -/
def readLRATProof (path : System.FilePath) : IO (Option (Array IntAction)) := do
  let proof ← IO.FS.readFile path
  match Parser.parseLines |>.run proof with
  | .ok actions => return some actions
  | .error .. => return none
