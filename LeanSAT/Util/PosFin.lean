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

instance {n : Nat} : CoeOut (PosFin n) Nat where
  coe := fun p => p.1

instance {n : Nat} : ToString (PosFin n) where
  toString := fun n => s!"{n.1}"
