import LeanSAT.Reflect.Tactics.BVDecide
import Std.Data.BitVec.Basic

open Std BitVec


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

example (h : 0#1 = 1#1) : False := by bv_decide

/-
I now have to write a meta program that uses `h` to:
1. translate it into `expr : BVLogicalExpr := .literal (.bin (.const 0#1) .eq (.const 1#1))`
2. Show that expr.eval [] = true

Concrete idea for doing this for the general `.literal case`:
1. Hand the expression over to a parser that created the `BVPred`
2. + returns a proof that `pred.eval [] = true`
3. Based on that we should be trivially be able to show that `.literal bvpred` evaluates to true
-/
