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

theorem foo (h : 0#1 = 1#1) : False := by bv_decide

#print foo


