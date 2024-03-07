/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.Reflect.Tactics.SatDecide

open Lean Meta

namespace BVDecide

-- TODO: This should be upstream?
instance : ToExpr (BitVec w) where
  toExpr bv := mkApp2 (mkConst ``BitVec.ofNat) (toExpr w) (toExpr bv.toNat)
  toTypeExpr := mkApp (mkConst ``BitVec) (toExpr w)

instance : ToExpr BVBinPred where
  toExpr x :=
    match x with
    | .eq => mkConst ``BVBinPred.eq
    | .neq => mkConst ``BVBinPred.neq
  toTypeExpr := mkConst ``BVBinPred

instance : ToExpr BVUnOp where
  toExpr x :=
    match x with
    | .not => mkConst ``BVUnOp.not
  toTypeExpr := mkConst ``BVUnOp

instance : ToExpr BVBinOp where
  toExpr x :=
    match x with
    | .and => mkConst ``BVBinOp.and
  toTypeExpr := mkConst ``BVBinOp

instance : ToExpr (BVExpr w) where
  toExpr x := go x
  toTypeExpr := mkApp (mkConst ``BVExpr) (toExpr w)
where
  go : BVExpr w → Expr
| .var idx => mkApp2 (mkConst ``BVExpr.var) (toExpr w) (toExpr idx)
| .const val => mkApp2 (mkConst ``BVExpr.const) (toExpr w) (toExpr val)
| .bin lhs op rhs => mkApp4 (mkConst ``BVExpr.bin) (toExpr w) (go lhs) (toExpr op) (go rhs)
| .un op operand => mkApp3 (mkConst ``BVExpr.un) (toExpr w) (toExpr op) (go operand)

instance : ToExpr BVPred where
  toExpr x := go x
  toTypeExpr := mkConst ``BVPred
where
  go : BVPred → Expr
  | .bin (w := w) lhs op rhs =>
    mkApp4 (mkConst ``BVPred.bin) (toExpr w) (toExpr lhs) (toExpr op) (toExpr rhs)

instance : ToExpr BVLogicalExpr where
  toExpr x := go x
  toTypeExpr := mkConst ``BVLogicalExpr
where
  go : BVLogicalExpr → Expr
  | .literal pred => mkApp2 (mkConst ``BoolExpr.literal) (toTypeExpr BVPred) (toExpr pred)
  | .const b => mkApp2 (mkConst ``BoolExpr.const) (toTypeExpr BVPred) (toExpr b)
  | .not x => mkApp2 (mkConst ``BoolExpr.not) (toTypeExpr BVPred) (go x)
  | .gate g x y => mkApp4 (mkConst ``BoolExpr.gate) (toTypeExpr BVPred) (toExpr g) (go x) (go y)


/--
The state of the reflection monad
-/
structure State where
  /--
  The atoms encountered so far. Saved as a map from `BitVec` expressions to a
  width × atomNumber pair.
  -/
  atoms : HashMap Expr (Nat × Nat) := {}

/--
The reflection monad, used to track `BitVec` variables that we see as we traverse
the context.
-/
abbrev M := StateRefT State MetaM

namespace M

/--
Run a reflection computation as a `MetaM` one.
-/
def run (m : M α) : MetaM α :=
  m.run' { } { }

/--
Retrieve the atoms as pairs of their width and expression.
-/
def atoms : M (List (Nat × Expr)) :=
  return (← getThe State).atoms.toArray.qsort (·.2.2 < ·.2.2) |>.map (fun (expr, width, _) => (width, expr)) |>.toList

/--
Retrieve a `BitVec.Assignment` representing the atoms we found so far.
-/
def atomsAssignment : M Expr := do
  let as ← atoms
  let packed : List Expr := as.map (fun (width, expr) => mkApp2 (mkConst ``BVExpr.PackedBitVec.mk) (toExpr width) expr)
  let packedType := mkConst ``BVExpr.PackedBitVec
  mkListLit packedType packed

-- TODO: we could store `evalFunc` in `HoldsAtAtoms` and maybe even fill it out with typeclass stuff
def mkEvalExpr (evalFunc : Name) (expr : Expr) : M Expr := do
  return mkApp2 (mkConst evalFunc) (← M.atomsAssignment) expr

end M

/--
A reified version of an `Expr` representing a `BVExpr`.
-/
structure ReifiedBVExpr (w : Nat) where
  /--
  The reified expression.
  -/
  bvExpr : BVExpr w
  /--
  A proof that `bvExpr.eval atomsAssignment = originalBVExpr`.
  -/
  evalsAtAtoms : M Expr
  /--
  A cache for `toExpr bvExpr`.
  -/
  expr : Expr

namespace ReifiedBVExpr

def mkEvalExpr (w : Nat) (expr : Expr) : M Expr := do
  return mkApp3 (mkConst ``BVExpr.eval) (toExpr w) (← M.atomsAssignment) expr

def mkBVRefl (w : Nat) (expr : Expr) : Expr :=
  mkApp2
   (mkConst ``Eq.refl [1])
   (mkApp (mkConst ``BitVec) (toExpr w))
   expr

/--
Reify an `Expr` that's a `BitVec`.
-/
def of (x : Expr) : M (Option (ReifiedBVExpr w)) := do
  -- TODO: should I do some whnf operation here? I think I should
  match x.getAppFnArgs with
  | (``BitVec.ofNat, #[_, _]) | (``OfNat.ofNat, #[_, _, _]) =>
    let some ⟨width, bvVal⟩ ← getBitVecValue? x | return none
    if h:width = w then
      let bvExpr := .const (h ▸ bvVal)
      let expr := mkApp2 (mkConst ``BVExpr.const) (toExpr w) (toExpr bvVal)
      let proof := do
        let evalExpr ← mkEvalExpr w expr
        return mkBVRefl w evalExpr
      return some ⟨bvExpr, proof, expr⟩
    else
      panic! "Attempt to reify ill-typed BitVec literal"
  | _ => return none

end ReifiedBVExpr

/--
A reified version of an `Expr` representing a `BVPred`.
-/
structure ReifiedBVPred where
  /--
  The reified expression.
  -/
  bvPred : BVPred
  /--
  A proof that `bvPred.eval atomsAssignment = true`.
  -/
  holdsAtAtoms : M Expr
  /--
  A cache for `toExpr bvPred`
  -/
  expr : Expr

namespace ReifiedBVPred

theorem beq_eq_true_of_eq {x y : BitVec w} (h : x = y) : (x == y) = true := (beq_iff_eq x y).mpr h
theorem bne_eq_true_of_ne {x y : BitVec w} (h : x ≠ y) : (x != y) = true := (bne_iff_ne x y).mpr h

theorem eq_congr (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) (h3 : lhs = rhs)
    : lhs' = rhs' := by
  simp[*]

theorem ne_congr (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) (h3 : lhs ≠ rhs)
    : lhs' ≠ rhs' := by
  simp[*]

/--
Reify an `Expr` that is a proof of a predicate about `BitVec`.
-/
def of (h : Expr) : M (Option ReifiedBVPred) := do
  let t ← instantiateMVars (← whnfR (← inferType h))
  match t.getAppFnArgs with
  | (``Not, #[w]) =>
    match w.getAppFnArgs with
    | (``Eq, #[.app (.const ``BitVec []) widthExpr, lhsExpr, rhsExpr]) =>
      let some ⟨width, lhs, rhs⟩ ← extractEq widthExpr lhsExpr rhsExpr | return none
      let bvExpr := .bin (w := width) lhs.bvExpr .neq rhs.bvExpr
      let expr := mkApp4 (mkConst ``BVPred.bin) widthExpr lhs.expr (mkConst ``BVBinPred.neq) rhs.expr
      let proof := do
        let lhsEval ← ReifiedBVExpr.mkEvalExpr width lhs.expr
        let lhsProof ← lhs.evalsAtAtoms
        let rhsEval ← ReifiedBVExpr.mkEvalExpr width rhs.expr
        let rhsProof ← rhs.evalsAtAtoms
        let neqProof :=
          mkApp8 (mkConst ``ne_congr) (toExpr width) lhsExpr rhsExpr lhsEval rhsEval lhsProof rhsProof h
        return mkApp4
          (mkConst ``bne_eq_true_of_ne)
          (toExpr width)
          lhsEval
          rhsEval
          neqProof
      return some ⟨bvExpr, proof, expr⟩
    | _ => return none
  | (``Eq, #[.app (.const ``BitVec []) widthExpr, lhsExpr, rhsExpr]) =>
    let some ⟨width, lhs, rhs⟩ ← extractEq widthExpr lhsExpr rhsExpr | return none
    let bvExpr := .bin (w := width) lhs.bvExpr .eq rhs.bvExpr
    let expr := mkApp4 (mkConst ``BVPred.bin) widthExpr lhs.expr (mkConst ``BVBinPred.eq) rhs.expr
    let proof := do
      let lhsEval ← ReifiedBVExpr.mkEvalExpr width lhs.expr
      let lhsProof ← lhs.evalsAtAtoms
      let rhsEval ← ReifiedBVExpr.mkEvalExpr width rhs.expr
      let rhsProof ← rhs.evalsAtAtoms
      let eqProof :=
        mkApp8 (mkConst ``eq_congr) (toExpr width) lhsExpr rhsExpr lhsEval rhsEval lhsProof rhsProof h
      return mkApp4 (mkConst ``beq_eq_true_of_eq) (toExpr width) lhsEval rhsEval eqProof
    return some ⟨bvExpr, proof, expr⟩
  | _ => return none
where
  extractEq (widthExpr lhsExpr rhsExpr : Expr) : M (Option ((w : Nat) × ReifiedBVExpr w × ReifiedBVExpr w)) := do
    let some width ← getNatValue? widthExpr | return none
    let some lhs ← ReifiedBVExpr.of lhsExpr | return none
    let some rhs ← ReifiedBVExpr.of rhsExpr | return none
    return some ⟨width, lhs, rhs⟩

end ReifiedBVPred

/--
A reified version of an `Expr` representing a `BVLogicalExpr`.
-/
structure ReifiedBVLogical where
  /--
  The reified expression.
  -/
  bvExpr : BVLogicalExpr
  /--
  A proof that `bvExpr.eval atomsAssignment = true`.
  -/
  holdsAtAtoms : M Expr
  /--
  A cache for `toExpr bvExpr`
  -/
  expr : Expr


namespace ReifiedBVLogical

def mkRefl (expr : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) expr

def mkTrans (x y z : Expr) (hxy hyz : Expr) : Expr :=
  mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``Bool) x y z hxy hyz

/--
Reify an `Expr` that is a proof of some boolean structure on top of predicates about `BitVec`s.
-/
partial def of (h : Expr) : M (Option ReifiedBVLogical) := do
  -- TODO: naive approach, does not handle any boolean structure on top of our problem.
  let t ← instantiateMVars (← whnfR (← inferType h))
  match t.getAppFnArgs with
  | (``Not, #[w]) =>
    match w.getAppFnArgs with
    | (``Eq, #[.app (.const ``BitVec []) _, _, _]) => goPred h
    -- TODO: might want support for other negations in the future
    | _ => return none
  | _ => goPred h
where
  goPred (h : Expr) : M (Option ReifiedBVLogical) := do
    let some pred ← ReifiedBVPred.of h | return none
    let bvExpr := .literal pred.bvPred
    let expr := mkApp2 (mkConst ``BoolExpr.literal) (mkConst ``BVPred) pred.expr
    let proof := do
      let evalLogic ← M.mkEvalExpr ``BVLogicalExpr.eval expr
      let evalPred ← M.mkEvalExpr ``BVPred.eval pred.expr
      let predProof ← pred.holdsAtAtoms
      return mkTrans evalLogic evalPred (mkConst ``Bool.true) (mkRefl evalLogic) predProof
    return some ⟨bvExpr, proof, expr⟩

/--
The trivially true `BVLogicalExpr`.
-/
def trivial : ReifiedBVLogical where
  bvExpr := .const true
  expr := toExpr (.const true : BVLogicalExpr)
  holdsAtAtoms := return mkApp (mkConst ``BVLogicalExpr.sat_true) (← M.atomsAssignment)

/--
Logical conjunction of two `ReifiedBVLogical`.
-/
def and (x y : ReifiedBVLogical) : ReifiedBVLogical where
  bvExpr := .gate .and x.bvExpr y.bvExpr
  expr := mkApp4 (mkConst ``BoolExpr.gate) (mkConst ``BVPred) (mkConst ``Gate.and) x.expr y.expr
  holdsAtAtoms :=
    return mkApp5
      (mkConst ``BVLogicalExpr.sat_and)
      x.expr
      y.expr
      (← M.atomsAssignment)
      (← x.holdsAtAtoms)
      (← y.holdsAtAtoms)

/-- Given a proof that `x.expr.unsat`, produce a proof of `False`. -/
def proveFalse (x : ReifiedBVLogical) (h : Expr) : M Expr := do
  let atomsList ← M.atomsAssignment
  let evalExpr := mkApp2 (mkConst ``BVLogicalExpr.eval) atomsList x.expr
  return mkApp3
    (mkConst ``ReflectSat.SatAtAtoms.false_of_eq_true_of_eq_false)
    evalExpr
    (← x.holdsAtAtoms)
    (.app h atomsList)

end ReifiedBVLogical

/--
Given a goal `g`, which should be `False`, returns
* a `e : BVLogicalExpr` (representing the conjunction of all bitvec predicates in hypotheses of `g`)
* a function which takes an expression representing a proof of `e.unsat`,
  and returns a proof of `False` valid in the context of `g`.
-/
def reflectBV (g : MVarId) : M (BVLogicalExpr × (Expr → M Expr)) := g.withContext do
  let hyps ← getLocalHyps
  let sats ← hyps.filterMapM ReifiedBVLogical.of
  IO.println "reflected things:"
  IO.println <| sats.map (·.bvExpr)
  let sat := sats.foldl (init := ReifiedBVLogical.trivial) ReifiedBVLogical.and
  return (sat.bvExpr, sat.proveFalse)

/--
Close a goal by:
1. Turning it into a BitVec problem.
2. Using bitblasting to turn that into a SAT problem.
3. Running an external SAT solver on it and obtaining an LRAT proof from it.
4. Verifying the LRAT proof using proof by reflection.
-/
def _root_.Lean.MVarId.bvDecide (g : MVarId) (cfg : SatDecide.TacticContext) : MetaM Unit := M.run do
  let g' ← falseOrByContra g
  g'.withContext do
    let (bvLogicalExpr, f) ←
      withTraceNode `bv (fun _ => return "Reflecting goal into BVLogicalExpr") do
        reflectBV g'
    trace[bv] "Reflected bv logical expression: {bvLogicalExpr}"
    let aux := mkApp (mkConst ``BVLogicalExpr.unsat) (toExpr bvLogicalExpr)
    let unsatProof := mkApp2 (mkConst ``sorryAx [.zero]) aux (mkConst ``Bool.false)
    let proveFalse ← f unsatProof
    g'.assign proveFalse

@[inherit_doc _root_.Lean.MVarId.bvDecide]
syntax (name := bvDecideSyntax) "bv_decide" : tactic

end BVDecide

open Elab.Tactic
elab_rules : tactic
  | `(tactic| bv_decide) => do
    let cfg ← SatDecide.TacticContext.new (← SatDecide.mkTemp)
    liftMetaFinishingTactic fun g => g.bvDecide cfg
