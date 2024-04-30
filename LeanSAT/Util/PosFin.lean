/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.Util.Misc

def PosFin (n : Nat) := {x : Nat // 0 < x ∧ x < n}

instance {n : Nat} : DecidableEq (PosFin n) :=
  inferInstanceAs (DecidableEq {x : Nat // 0 < x ∧ x < n})

instance {n : Nat} : Hashable (PosFin n) where
  hash := fun x => hash x.1

instance {n : Nat} : BEq (PosFin n) where
  beq := fun x1 x2 => x1.1 == x2.1

instance {n : Nat} : LawfulBEq (PosFin n) where
  eq_of_beq := by
    intro a b h
    rw [BEq.beq, instBEqPosFin] at h
    simp only at h
    rw [beq_iff_eq] at h
    rw [Misc.Subtype.ext_iff]
    exact h
  rfl := by
    intro a
    rw [BEq.beq, instBEqPosFin]
    simp only [beq_self_eq_true]

instance {n : Nat} : CoeOut (PosFin n) Nat where
  coe := fun p => p.1

instance {n : Nat} : ToString (PosFin n) where
  toString := fun n => s!"{n.1}"
