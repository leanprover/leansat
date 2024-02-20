import Std.Data.List.Init.Lemmas

@[simp] theorem List.all_append {x y : List α} : (x ++ y).all f = (x.all f && y.all f) := by
  induction x with
  | nil => rfl
  | cons h t ih => simp_all [Bool.and_assoc]
