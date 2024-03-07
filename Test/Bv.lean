import LeanSAT.Reflect.Tactics.BVDecide

open BitVec

/-
BVExpr w ↔ Std.BitVec w
BVPred ↔ `Prop` that comes from predicates on `Std.BitVec`s
BVLogicalExpr ↔ logical structure on top of `Prop`s represented by `BVPred`


First approximation of tactic:
- Do not handle anything on the BVLogicalExpr level apart from literals of BVPred
- Handle only equality of Std.BitVec at a BVPred level
- Handle only constants on BVExpr level

next extensions:
- Add support for negation at BVLogicalExpr level
- Handle variables at BVExpr
- Handle bitwise and at BVExpr
- Handle bitwise not at BVExpr
-/

set_option trace.bv true in
theorem foo (h1 : 0#1 = 1#1) (h2 : (2 : BitVec 2) = 3) (h3 : x = 4#3)
    (h4 : x &&& y = y &&& x) : 4#5 = 5#5 := by
  bv_decide

set_option trace.bv true in
theorem all_features {x y : BitVec 10} (h : x = y) : x &&& 1 = y &&& 1#10 := by
  bv_decide
