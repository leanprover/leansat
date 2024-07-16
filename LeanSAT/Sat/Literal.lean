/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.Sat.Basic

abbrev Literal (α : Type u) := α × Bool

namespace Literal

open Sat

instance [Hashable α] : Hashable (Literal α) where
  hash := fun x => if x.2 then hash x.1 else hash x.1 + 1

instance : HSat α (Literal α) where
  eval := fun p l => (p l.1) = l.2

instance (p : α → Bool) (l : Literal α) : Decidable (p ⊨ l) := by
  rw [HSat.eval, instHSat]
  exact Bool.decEq (p l.fst) l.snd

def negateLiteral (l : Literal α) := (l.1, not l.2)

def dimacs [ToString α] (l : Literal α) : String :=
  if l.2 then
    s!"{l.1}"
  else
    s!"-{l.1}"

end Literal
