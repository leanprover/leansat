/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.AIG.Cached
import LeanSAT.AIG.CachedLemmas

/-!
This module contains functions to construct basic logic gates while making use of the sub-circuit
cache if possible.
-/

namespace AIG

variable {α : Type} [BEq α] [Hashable α] [DecidableEq α]

/--
Create a not gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkNotCached (gate : Nat) (aig : AIG α) (hgate : gate < aig.decls.size) : Entrypoint α :=
  -- ¬x = true && invert x
  let constEntry := aig.mkConstCached true
  have := aig.mkConstCached_le_size true
  constEntry.aig.mkGateCached
    constEntry.start
    gate
    false
    true
    constEntry.inv
    (by apply lt_mkConstCached_size_of_lt_aig_size _ _ hgate)

/--
Create an and gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkAndCached (lhs rhs : Nat) (aig : AIG α) (hl : lhs < aig.decls.size) (hr : rhs < aig.decls.size) : Entrypoint α :=
  aig.mkGateCached lhs rhs false false hl hr

/--
Create an or gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkOrCached (lhs rhs : Nat) (aig : AIG α) (hl : lhs < aig.decls.size) (hr : rhs < aig.decls.size) : Entrypoint α :=
  -- x or y = true && (invert (invert x && invert y))
  let auxEntry := aig.mkGateCached lhs rhs true true hl hr
  let constEntry := auxEntry.aig.mkConstCached true
  constEntry.aig.mkGateCached
    constEntry.start
    auxEntry.start
    false
    true
    constEntry.inv
    (by apply lt_mkConstCached_size)

/--
Create an xor gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkXorCached (lhs rhs : Nat) (aig : AIG α) (hl : lhs < aig.decls.size) (hr : rhs < aig.decls.size) : Entrypoint α :=
  -- x xor y = (invert (invert (x && y))) && (invert ((invert x) && (invert y)))
  let aux1Entry := aig.mkGateCached lhs rhs false false hl hr
  have := aig.mkGateCached_le_size _ _ false false hl hr
  have h3 : lhs < aux1Entry.aig.decls.size := by
    dsimp [aux1Entry] at *
    omega
  let aux2Entry := aux1Entry.aig.mkGateCached
      lhs
      rhs
      true
      true
      h3
      (by apply lt_mkGateCached_size_of_lt_aig_size; omega)
  aux2Entry.aig.mkGateCached aux1Entry.start aux2Entry.start true true (by apply lt_mkGateCached_size) aux2Entry.inv

/--
Create an equality gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkBEqCached (lhs rhs : Nat) (aig : AIG α) (hl : lhs < aig.decls.size) (hr : rhs < aig.decls.size) : Entrypoint α :=
  -- a == b = (invert (a && (invert b))) && (invert ((invert a) && b))
  let aux1Entry := aig.mkGateCached lhs rhs false true hl hr
  have := aig.mkGateCached_le_size _ _ false true hl hr
  have h3 : lhs < aux1Entry.aig.decls.size := by
    dsimp [aux1Entry] at *
    omega
  let aux2Entry :=
    aux1Entry.aig.mkGateCached
      lhs
      rhs
      true
      false
      h3
      (by apply lt_mkGateCached_size_of_lt_aig_size; omega)
  aux2Entry.aig.mkGateCached
    aux1Entry.start
    aux2Entry.start
    true
    true
    (by apply lt_mkGateCached_size)
    aux2Entry.inv

/--
Create an implication gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkImpCached (lhs rhs : Nat) (aig : AIG α) (hl : lhs < aig.decls.size) (hr : rhs < aig.decls.size) : Entrypoint α :=
  -- a -> b = true && (invert (a and (invert b)))
  let auxEntry :=
    aig.mkGateCached
      lhs
      rhs
      false
      true
      hl
      hr
  have := aig.mkGateCached_le_size _ _ false true hl hr
  let constEntry := mkConstCached true auxEntry.aig
  have := auxEntry.aig.mkConstCached_le_size true
  constEntry.aig.mkGateCached
    constEntry.start
    auxEntry.start
    false
    true
    constEntry.inv
    (by apply lt_mkConstCached_size)

end AIG
