/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
namespace LRAT

structure ByteArray.Iterator where
  arr : ByteArray
  pos : Nat
  deriving Inhabited

namespace ByteArray.Iterator

def fresh (arr : ByteArray) : ByteArray.Iterator :=
  { arr := arr, pos := 0 }

@[inline]
def next (it : Iterator) : Iterator :=
  let ⟨arr, pos⟩ := it
  ⟨arr, pos + 1⟩

@[inline]
def curr (it : Iterator) : UInt8 :=
  let ⟨arr, pos⟩ := it
  if h:pos < arr.size then
    arr[pos]'h
  else
    default

@[inline]
def hasNext (it : Iterator) : Bool :=
  let ⟨arr, pos⟩ := it
  pos < arr.size

end ByteArray.Iterator

inductive Parsec.ParseResult (α : Type) (s : Type) where
  | success (pos : s) (res : α)
  | error (pos : s) (err : String)
  deriving Repr

def Parsec (s : Type) (α : Type) : Type := s → Parsec.ParseResult α s

namespace Parsec

class Stream (s : Type) (elem : outParam Type) (idx : outParam Type) [DecidableEq idx] [ToString elem] [DecidableEq elem] where
  pos : s → idx
  next : s → s
  curr : s → elem
  hasNext : s → Bool

instance : Stream String.Iterator Char String.Pos where
  pos it := it.pos
  next it := it.next
  curr it := it.curr
  hasNext it := it.hasNext

instance : Stream ByteArray.Iterator UInt8 Nat where
  pos it := it.pos
  next it := it.next
  curr it := it.curr
  hasNext it := it.hasNext

instance : Inhabited (Parsec s α) where
  default := fun it => .error it ""

@[inline]
protected def pure (a : α) : Parsec s α := fun it =>
 .success it a

@[inline]
def bind (f : Parsec s α) (g : α → Parsec s β) : Parsec s β := λ it =>
  match f it with
  | .success rem a => g a rem
  | .error pos msg => .error pos msg

instance : Monad (Parsec s) where
  pure := Parsec.pure
  bind := bind

@[inline]
def fail (msg : String) : Parsec s α := fun it =>
  .error it msg

variable [DecidableEq idx] [ToString elem] [DecidableEq elem] [Stream s elem idx]

@[inline]
def tryCatch (p : Parsec s α)
    (csuccess : α → Parsec s β)
    (cerror : Unit → Parsec s β)
    : Parsec s β := fun it =>
  match p it with
  | .success rem a => csuccess a rem
  | .error rem err =>
    if Stream.pos it = Stream.pos rem then cerror () rem else .error rem err

@[inline]
def orElse (p : Parsec s α) (q : Unit → Parsec s α) : Parsec s α :=
  tryCatch p pure q

@[inline]
def attempt (p : Parsec s α) : Parsec s α := fun it =>
  match p it with
  | .success rem res => .success rem res
  | .error _ err => .error it err

instance : Alternative (Parsec s) where
  failure := fail ""
  orElse := orElse

protected def run [Repr idx] (p : Parsec s α) (input : s) : Except String α :=
  match p input with
  | Parsec.ParseResult.success _ res => Except.ok res
  | Parsec.ParseResult.error it err  => Except.error s!"offset {repr (Stream.pos it)}: {err}"

def expectedEndOfInput := "expected end of input"

@[inline]
def eof : Parsec s Unit := fun it =>
  if Stream.hasNext it then
    .error it expectedEndOfInput
  else
    .success it ()

@[specialize]
partial def manyCore (p : Parsec s α) (acc : Array α) : Parsec s (Array α) :=
  tryCatch p (manyCore p <| acc.push ·) (fun _ => pure acc)

@[inline]
def many (p : Parsec s α) : Parsec s (Array α) := manyCore p #[]

@[inline]
def many1 (p : Parsec s α) : Parsec s (Array α) := do manyCore p #[← p]

def unexpectedEndOfInput := "unexpected end of input"

@[inline]
def anyChar : Parsec s elem := fun it =>
  if Stream.hasNext it then .success (Stream.next it) (Stream.curr it) else .error it unexpectedEndOfInput

@[inline]
def pchar (c : elem) : Parsec s elem := attempt do
  if (← anyChar) = c then pure c else fail s!"expected: '{c}'"

@[inline]
def skipElem (c : elem) : Parsec s Unit := pchar c *> pure ()

@[inline]
def satisfy (p : elem → Bool) : Parsec s elem := attempt do
  let c ← anyChar
  if p c then return c else fail "condition not satisfied"

@[inline]
def notFollowedBy (p : Parsec s α) : Parsec s Unit := fun it =>
  match p it with
  | .success _ _ => .error it ""
  | .error _ _ => .success it ()

@[inline]
def peek? : Parsec s (Option elem) := fun it =>
  if Stream.hasNext it then
    .success it (Stream.curr it)
  else
    .success it none

@[inline]
def peek! : Parsec s elem := do
  let some c ← peek? | fail unexpectedEndOfInput
  return c

@[inline]
def skip : Parsec s Unit := fun it =>
  .success (Stream.next it) ()

@[inline]
def eof? : Parsec s Bool := fun it =>
  .success it (!Stream.hasNext it)

namespace Byte

@[inline]
def digit : Parsec ByteArray.Iterator UInt8 := attempt do
  let c ← anyChar
  if '0'.toNat.toUInt8 ≤ c ∧ c ≤ '9'.toNat.toUInt8 then return c else fail s!"digit expected"

@[inline]
def digitToNat (b : UInt8) : Nat := (b - '0'.toNat.toUInt8).toNat

@[inline]
partial def digitsCore (acc : Nat) : Parsec ByteArray.Iterator Nat := fun it =>
  /-
  This used to be:
  Parsec.tryCatch digit (fun digit => parseDigitsCore (acc * 10 + digitToNat digit)) (fun _ => pure acc)
  But this code keeps on allocating success/error values in the hot loop, we don't want that.
  -/
  let ⟨res, it⟩ := go it acc
  .success it res
where
  go (it : ByteArray.Iterator) (acc : Nat) : (Nat × ByteArray.Iterator) :=
    if it.hasNext then
      let candidate := it.curr
      -- TODO: prettier
      if '0'.toNat.toUInt8 ≤ candidate ∧ candidate ≤ '9'.toNat.toUInt8 then
        let digit := digitToNat candidate
        let acc := acc * 10 + digit
        go it.next acc
      else
        (acc, it)
    else
      (acc, it)

@[inline]
def digits : Parsec ByteArray.Iterator Nat := do
  let d ← digit
  digitsCore (digitToNat d)

@[inline]
def skipChar (c : Char) : Parsec ByteArray.Iterator Unit := pchar c.toNat.toUInt8 *> pure ()

def skipString (s : String) : Parsec ByteArray.Iterator Unit := do
  let arr := s.toUTF8
  for byte in arr do
    skipElem byte

end Byte

end Parsec

end LRAT
