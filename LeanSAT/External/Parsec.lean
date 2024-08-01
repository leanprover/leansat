/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/

namespace ByteArray

/-- Iterator over the bytes (`UInt8`) of a `ByteArray`.

Typically created by `arr.iter`, where `arr` is a `ByteArray`.

An iterator is *valid* if the position `i` is *valid* for the array `arr`, meaning `0 ≤ i ≤ arr.size`

Most operations on iterators return arbitrary values if the iterator is not valid. The functions in
the `ByteArray.Iterator` API should rule out the creation of invalid iterators, with two exceptions:

- `Iterator.next iter` is invalid if `iter` is already at the end of the array (`iter.atEnd` is
  `true`)
- `Iterator.forward iter n`/`Iterator.nextn iter n` is invalid if `n` is strictly greater than the
  number of remaining bytes.
-/
structure Iterator where
  /-- The array the iterator is for. -/
  array : ByteArray
  /-- The current position.

  This position is not necessarily valid for the array, for instance if one keeps calling
  `Iterator.next` when `Iterator.atEnd` is true. If the position is not valid, then the
  current byte is `(default : UInt8)`. -/
  idx : Nat
  deriving Inhabited

/-- Creates an iterator at the beginning of an array. -/
def mkIterator (arr : ByteArray) : Iterator :=
  ⟨arr, 0⟩

@[inherit_doc mkIterator]
abbrev iter := mkIterator

/-- The size of an array iterator is the number of bytes remaining. -/
instance : SizeOf Iterator where
  sizeOf i := i.array.size - i.idx

theorem Iterator.sizeOf_eq (i : Iterator) : sizeOf i = i.array.size - i.idx :=
  rfl

namespace Iterator

/-- Number of bytes remaining in the iterator. -/
def remainingBytes : Iterator → Nat
  | ⟨arr, i⟩ => arr.size - i

@[inherit_doc Iterator.idx]
def pos := Iterator.idx

/-- The byte at the current position.

On an invalid position, returns `(default : UInt8)`. -/
@[inline]
def curr : Iterator → UInt8
  | ⟨arr, i⟩ =>
    if h:i < arr.size then
      arr[i]'h
    else
      default

/-- Moves the iterator's position forward by one byte, unconditionally.

It is only valid to call this function if the iterator is not at the end of the array, *i.e.*
`Iterator.atEnd` is `false`; otherwise, the resulting iterator will be invalid. -/
@[inline]
def next : Iterator → Iterator
  | ⟨arr, i⟩ => ⟨arr, i + 1⟩

/-- Decreases the iterator's position.

If the position is zero, this function is the identity. -/
@[inline]
def prev : Iterator → Iterator
  | ⟨arr, i⟩ => ⟨arr, i - 1⟩

/-- True if the iterator is past the array's last byte. -/
@[inline]
def atEnd : Iterator → Bool
  | ⟨arr, i⟩ => i ≥ arr.size

/-- True if the iterator is not past the array's last byte. -/
@[inline]
def hasNext : Iterator → Bool
  | ⟨arr, i⟩ => i < arr.size

/-- True if the position is not zero. -/
@[inline]
def hasPrev : Iterator → Bool
  | ⟨_, i⟩ => i > 0

/-- Moves the iterator's position to the end of the array.

Note that `i.toEnd.atEnd` is always `true`. -/
@[inline]
def toEnd : Iterator → Iterator
  | ⟨arr, _⟩ => ⟨arr, arr.size⟩

/-- Moves the iterator's position several bytes forward.

The resulting iterator is only valid if the number of bytes to skip is less than or equal to
the number of bytes left in the iterator. -/
@[inline]
def forward : Iterator → Nat → Iterator
  | ⟨arr, i⟩, f => ⟨arr, i + f⟩

@[inherit_doc forward, inline]
def nextn : Iterator → Nat → Iterator := forward

/-- Moves the iterator's position several bytes back.

If asked to go back more bytes than available, stops at the beginning of the array. -/
@[inline]
def prevn : Iterator → Nat → Iterator
  | ⟨arr, i⟩, f => ⟨arr, i - f⟩

end Iterator
end ByteArray

namespace LRAT
namespace Parsec

inductive ParseResult (α : Type) (ι : Type) where
  | success (pos : ι) (res : α)
  | error (pos : ι) (err : String)
  deriving Repr

end Parsec

def Parsec (ι : Type) (α : Type) : Type := ι → Parsec.ParseResult α ι

namespace Parsec

class Input (ι : Type) (elem : outParam Type) (idx : outParam Type) [DecidableEq idx] [DecidableEq elem] where
  pos : ι → idx
  next : ι → ι
  curr : ι → elem
  hasNext : ι → Bool

variable {α : Type} {ι : Type} {elem : Type} {idx : Type}
variable [DecidableEq idx] [DecidableEq elem] [Input ι elem idx]

instance : Inhabited (Parsec ι α) where
  default := fun it => .error it ""

@[inline]
protected def pure (a : α) : Parsec ι α := fun it =>
  .success it a

@[inline]
def bind {α β : Type} (f : Parsec ι α) (g : α → Parsec ι β) : Parsec ι β := fun it =>
  match f it with
  | .success rem a => g a rem
  | .error pos msg => .error pos msg

instance : Monad (Parsec ι) where
  pure := Parsec.pure
  bind := Parsec.bind

@[inline]
def fail (msg : String) : Parsec ι α := fun it =>
  .error it msg

@[inline]
def tryCatch (p : Parsec ι α) (csuccess : α → Parsec ι β) (cerror : Unit → Parsec ι β)
    : Parsec ι β := fun it =>
  match p it with
  | .success rem a => csuccess a rem
  | .error rem err =>
    -- We assume that it.s never changes as the `Parsec` monad only modifies `it.pos`.
    if Input.pos it = Input.pos rem then cerror () rem else .error rem err

@[inline]
def orElse (p : Parsec ι α) (q : Unit → Parsec ι α) : Parsec ι α :=
  tryCatch p pure q

@[inline]
def attempt (p : Parsec ι α) : Parsec ι α := fun it =>
  match p it with
  | .success rem res => .success rem res
  | .error _ err => .error it err

instance : Alternative (Parsec ι) where
  failure := fail ""
  orElse := orElse

def expectedEndOfInput := "expected end of input"

@[inline]
def eof : Parsec ι Unit := fun it =>
  if Input.hasNext it then
    .error it expectedEndOfInput
  else
    .success it ()

@[specialize]
partial def manyCore (p : Parsec ι α) (acc : Array α) : Parsec ι <| Array α :=
  tryCatch p (manyCore p <| acc.push ·) (fun _ => pure acc)

@[inline]
def many (p : Parsec ι α) : Parsec ι <| Array α := manyCore p #[]

@[inline]
def many1 (p : Parsec ι α) : Parsec ι <| Array α := do manyCore p #[← p]

def unexpectedEndOfInput := "unexpected end of input"

@[inline]
def any : Parsec ι elem := fun it =>
  if Input.hasNext it then
    .success (Input.next it) (Input.curr it)
  else
    .error it unexpectedEndOfInput

@[inline]
def satisfy (p : elem → Bool) : Parsec ι elem := attempt do
  let c ← any
  if p c then return c else fail "condition not satisfied"

@[inline]
def notFollowedBy (p : Parsec ι α) : Parsec ι Unit := fun it =>
  match p it with
  | .success _ _ => .error it ""
  | .error _ _ => .success it ()

@[inline]
def peek? : Parsec ι (Option elem) := fun it =>
  if Input.hasNext it then
    .success it (Input.curr it)
  else
    .success it none

@[inline]
def peek! : Parsec ι elem := do
  let some c ← peek? | fail unexpectedEndOfInput
  return c

@[inline]
def skip : Parsec ι Unit := fun it =>
  .success (Input.next it) ()

@[specialize]
partial def manyCharsCore (p : Parsec ι Char) (acc : String) : Parsec ι String :=
  tryCatch p (manyCharsCore p <| acc.push ·) (fun _ => pure acc)

@[inline]
def manyChars (p : Parsec ι Char) : Parsec ι String := manyCharsCore p ""

@[inline]
def many1Chars (p : Parsec ι Char) : Parsec ι String := do manyCharsCore p (← p).toString

def eof? : Parsec ι Bool := fun it =>
  .success it (!Input.hasNext it)

namespace ByteArray

instance : Input ByteArray.Iterator UInt8 Nat where
  pos it := it.pos
  next it := it.next
  curr it := it.curr
  hasNext it := it.hasNext

abbrev Parser (α : Type) : Type := Parsec ByteArray.Iterator α

protected def Parser.run (p : Parser α) (arr : ByteArray) : Except String α :=
  match p arr.iter with
  | .success _ res => Except.ok res
  | .error it err  => Except.error s!"offset {repr it.pos}: {err}"

@[inline]
def digit : Parsec ByteArray.Iterator UInt8 := attempt do
  let c ← any
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
def pbyte (b : UInt8) : Parser UInt8 := attempt do
  if (← any) = b then pure b else fail s!"expected: '{b}'"

@[inline]
def skipByte (b : UInt8) : Parser Unit := pbyte b *> pure ()

def skipBytes (arr : ByteArray) : Parser Unit := do
  for b in arr do
    skipByte b

@[inline]
def pstring (s : String) : Parser String := do
  skipBytes s.toUTF8
  return s

@[inline]
def skipString (s : String) : Parser Unit := pstring s *> pure ()

/--
Parse a `Char` that can be represented in 1 byte. If `c` uses more than 1 byte it is truncated.
-/
@[inline]
def pByteChar (c : Char) : Parser Char := attempt do
  if (← any) = c.toUInt8 then pure c else fail s!"expected: '{c}'"

/--
Skip a `Char` that can be represented in 1 byte. If `c` uses more than 1 byte it is truncated.
-/
@[inline]
def skipByteChar (c : Char) : Parser Unit := skipByte c.toUInt8

private partial def skipWs (it : ByteArray.Iterator) : ByteArray.Iterator :=
  if it.hasNext then
    let b := it.curr
    if b = '\u0009'.toUInt8 ∨ b = '\u000a'.toUInt8 ∨ b = '\u000d'.toUInt8 ∨ b = '\u0020'.toUInt8 then
      skipWs it.next
    else
      it
  else
   it

@[inline]
def ws : Parser Unit := fun it =>
  .success (skipWs it) ()

def take (n : Nat) : Parser ByteArray := fun it =>
  let subarr := it.array.extract it.idx (it.idx + n)
  if subarr.size != n then
    .error it s!"expected: {n} bytes"
  else
    .success (it.forward n) subarr

end ByteArray
end Parsec
end LRAT
