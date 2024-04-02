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
  match h:aig.mkConstCached true with
  | ⟨taig, constEntry, hconst⟩ =>
    taig.mkGateCached
      {
        lhs := {
          ref := Ref.mk constEntry hconst
          inv := false
        }
        rhs := {
          ref := gate.cast <| by
            intros
            have : taig = (aig.mkConstCached true).aig := by simp[h]
            rw [this]
            apply LawfulOperator.lt_size_of_lt_aig_size (f := mkConstCached)
            assumption
          inv := true
        }
      }

structure BinaryInput (aig : AIG α) where
  lhs : Ref aig
  rhs : Ref aig

@[inline]
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
  let ⟨aig, auxEntry, haux⟩ := aig.mkGateCached <| input.asGateInput true true
  match h:aig.mkConstCached true with
  | ⟨caig, constEntry, hconst⟩ =>
    caig.mkGateCached
      {
        lhs := {
          ref := Ref.mk constEntry hconst
          inv := false
        },
        rhs := {
          ref := Ref.mk auxEntry haux |>.cast <| by
            intros
            have : caig = (aig.mkConstCached true).aig := by simp[h]
            rw [this]
            apply LawfulOperator.lt_size_of_lt_aig_size (f := mkConstCached)
            assumption
          inv := true
        }
      }

/--
Create an xor gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkXorCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- x xor y = (invert (invert (x && y))) && (invert ((invert x) && (invert y)))
  match h1:aig.mkGateCached <| input.asGateInput false false with
  | ⟨laig, aux1Entry, haux1⟩ =>
    have hlaig : laig = (aig.mkGateCached <| input.asGateInput false false).aig := by simp [h1]
    let rinput :=
      (input.asGateInput true true).cast
        (by
          intros
          rw [hlaig]
          apply LawfulOperator.lt_size_of_lt_aig_size (f := mkGateCached)
          assumption)
        (by
          intros
          rw [hlaig]
          apply LawfulOperator.lt_size_of_lt_aig_size (f := mkGateCached)
          assumption)
    match h2:laig.mkGateCached rinput with
    | ⟨raig, aux2Entry, haux2⟩ =>
      have hraig : raig = (laig.mkGateCached rinput).aig := by simp [h2]
      raig.mkGateCached
        {
          lhs := {
            ref := Ref.mk aux1Entry haux1 |>.cast <| by
              intro h
              rw [hraig]
              apply LawfulOperator.lt_size_of_lt_aig_size (f := mkGateCached)
              assumption
            inv := true
          },
          rhs := {
            ref := Ref.mk aux2Entry haux2
            inv := true
          }
        }

/--
Create an equality gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkBEqCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- a == b = (invert (a && (invert b))) && (invert ((invert a) && b))
  match h1:aig.mkGateCached <| input.asGateInput false true with
  | ⟨laig, aux1Entry, haux1⟩ =>
    have hlaig : laig = (aig.mkGateCached <| input.asGateInput false true).aig := by simp [h1]
    let rinput :=
      (input.asGateInput true false).cast
        (by
          intros
          rw [hlaig]
          apply LawfulOperator.lt_size_of_lt_aig_size (f := mkGateCached)
          assumption)
        (by
          intros
          rw [hlaig]
          apply LawfulOperator.lt_size_of_lt_aig_size (f := mkGateCached)
          assumption)
    match h2:laig.mkGateCached rinput with
    | ⟨raig, aux2Entry, haux2⟩ =>
      have hraig : raig = (laig.mkGateCached rinput).aig := by simp [h2]
      raig.mkGateCached
        {
          lhs := {
            ref := Ref.mk aux1Entry haux1 |>.cast <| by
              intro h
              rw [hraig]
              apply LawfulOperator.lt_size_of_lt_aig_size (f := mkGateCached)
              assumption
            inv := true
          },
          rhs := {
            ref := Ref.mk aux2Entry haux2
            inv := true
          }
        }

/--
Create an implication gate in the input AIG. This uses the builtin cache to enable automated subterm sharing
-/
def mkImpCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- a -> b = true && (invert (a and (invert b)))
  let ⟨aig, auxEntry, haux⟩ := aig.mkGateCached <| input.asGateInput false true
  match h:aig.mkConstCached true with
  | ⟨caig, constEntry, hconst⟩ =>
    caig.mkGateCached
      {
        lhs := {
          ref := Ref.mk constEntry hconst
          inv := false
        },
        rhs := {
          ref := Ref.mk auxEntry haux |>.cast <| by
            intros
            have : caig = (aig.mkConstCached true).aig := by simp[h]
            rw [this]
            apply LawfulOperator.lt_size_of_lt_aig_size (f := mkConstCached)
            assumption
          inv := true
        }
      }

end AIG
