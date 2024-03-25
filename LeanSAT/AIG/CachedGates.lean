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
def mkNotCached (aig : AIG α) (gate : Ref aig) : Entrypoint α :=
  -- ¬x = true && invert x
  let constEntry := aig.mkConstCached true
  have := aig.mkConstCached_le_size true
  constEntry.aig.mkGateCached
    {
      lhs := {
        ref := Ref.ofEntrypoint constEntry
        inv := false
      }
      rhs := {
        ref := gate.cast <| by
          intros
          apply LawfulOperator.lt_size_of_lt_aig_size (f := mkConstCached)
          assumption
        inv := true
      }
    }

structure BinaryInput (aig : AIG α) where
  lhs : Ref aig
  rhs : Ref aig

def BinaryInput.asGateInput {aig : AIG α} (input : BinaryInput aig) (linv rinv : Bool) : GateInput aig :=
  {
    lhs := {
      ref := input.lhs
      inv := linv
    },
    rhs := {
      ref := input.rhs
      inv := rinv
    }
  }

/--
Create an and gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkAndCached (aig : AIG α) (input : BinaryInput aig)  : Entrypoint α :=
  aig.mkGateCached <| input.asGateInput false false

/--
Create an or gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkOrCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- x or y = true && (invert (invert x && invert y))
  let auxEntry := aig.mkGateCached <| input.asGateInput true true
  let constEntry := auxEntry.aig.mkConstCached true
  constEntry.aig.mkGateCached
    {
      lhs := {
        ref := Ref.ofEntrypoint constEntry
        inv := false
      },
      rhs := {
        ref := Ref.ofEntrypoint auxEntry |>.cast <| by
          intros
          apply LawfulOperator.lt_size (f := mkConstCached)
        inv := true
      }
    }

/--
Create an xor gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkXorCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- x xor y = (invert (invert (x && y))) && (invert ((invert x) && (invert y)))
  let aux1Entry := aig.mkGateCached <| input.asGateInput false false
  let aux2Entry := aux1Entry.aig.mkGateCached <| (input.asGateInput true true).cast
    (by
      intros
      apply LawfulOperator.lt_size_of_lt_aig_size (f := mkGateCached)
      assumption)
    (by
      intros
      apply LawfulOperator.lt_size_of_lt_aig_size (f := mkGateCached)
      assumption)
  aux2Entry.aig.mkGateCached
    {
      lhs := {
        ref := Ref.ofEntrypoint aux1Entry |>.cast <| by
          intro h
          apply LawfulOperator.lt_size_of_lt_aig_size (f := mkGateCached)
          assumption
        inv := true
      },
      rhs := {
        ref := Ref.ofEntrypoint aux2Entry
        inv := true
      }
    }

/--
Create an equality gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkBEqCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- a == b = (invert (a && (invert b))) && (invert ((invert a) && b))
  let aux1Entry := aig.mkGateCached <| input.asGateInput false true
  let aux2Entry := aux1Entry.aig.mkGateCached <| (input.asGateInput true false).cast
    (by
      intros
      apply LawfulOperator.lt_size_of_lt_aig_size (f := mkGateCached)
      assumption)
    (by
      intros
      apply LawfulOperator.lt_size_of_lt_aig_size (f := mkGateCached)
      assumption)
  aux2Entry.aig.mkGateCached
    {
      lhs := {
        ref := Ref.ofEntrypoint aux1Entry |>.cast <| by
          intro h
          apply LawfulOperator.lt_size_of_lt_aig_size (f := mkGateCached)
          assumption
        inv := true
      },
      rhs := {
        ref := Ref.ofEntrypoint aux2Entry
        inv := true
      }
    }

/--
Create an implication gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkImpCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- a -> b = true && (invert (a and (invert b)))
  let auxEntry := aig.mkGateCached <| input.asGateInput false true
  let constEntry := auxEntry.aig.mkConstCached true
  constEntry.aig.mkGateCached
    {
      lhs := {
        ref := Ref.ofEntrypoint constEntry
        inv := false
      },
      rhs := {
        ref := Ref.ofEntrypoint auxEntry |>.cast <| by
          intros
          apply LawfulOperator.lt_size_of_lt_aig_size (f := mkConstCached)
          assumption
        inv := true
      }
    }

end AIG
