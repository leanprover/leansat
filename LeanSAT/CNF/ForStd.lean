/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

@[simp] theorem List.all_append {x y : List α} : (x ++ y).all f = (x.all f && y.all f) := by
  induction x with
  | nil => rfl
  | cons h t ih => simp_all [Bool.and_assoc]
