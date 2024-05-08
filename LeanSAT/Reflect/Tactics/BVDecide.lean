/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.Reflect.BVExpr.BitBlast
import LeanSAT.Reflect.Tactics.SatDecide
import LeanSAT.Reflect.Tactics.Normalize

import LeanSAT.LRAT.LRATChecker
import LeanSAT.LRAT.LRATCheckerSound
import LeanSAT.External.Solver

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
    | .shiftLeftConst n => mkApp (mkConst ``BVUnOp.shiftLeftConst) (toExpr n)
    | .shiftRightConst n => mkApp (mkConst ``BVUnOp.shiftRightConst) (toExpr n)
  toTypeExpr := mkConst ``BVUnOp

instance : ToExpr BVBinOp where
  toExpr x :=
    match x with
    | .and => mkConst ``BVBinOp.and
    | .or => mkConst ``BVBinOp.or
    | .xor => mkConst ``BVBinOp.xor
    | .add => mkConst ``BVBinOp.add
  toTypeExpr := mkConst ``BVBinOp

instance : ToExpr (BVExpr w) where
  toExpr x := go x
  toTypeExpr := mkApp (mkConst ``BVExpr) (toExpr w)
where
  go {w : Nat} : BVExpr w → Expr
| .var idx => mkApp2 (mkConst ``BVExpr.var) (toExpr w) (toExpr idx)
| .const val => mkApp2 (mkConst ``BVExpr.const) (toExpr w) (toExpr val)
| .zeroExtend (w := oldWidth) val inner =>
  mkApp3 (mkConst ``BVExpr.zeroExtend) (toExpr oldWidth) (toExpr val) (go inner)
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

/--
Look up an expression in the atoms, recording it if it has not previously appeared.
-/
def lookup (e : Expr) (width : Nat) : M Nat := do
  match (← getThe State).atoms.find? e with
  | some (width', ident) =>
    if width != width' then
      panic! "The same atom occurs with different widths, this is a bug"
    return ident
  | none =>
  trace[bv] "New atom of width {width}: {e}"
  let ident ← modifyGetThe State fun s =>
    (s.atoms.size, { s with atoms := s.atoms.insert e (width, s.atoms.size) })
  return ident

end M

/--
A reified version of an `Expr` representing a `BVExpr`.
-/
structure ReifiedBVExpr where
  width : Nat
  /--
  The reified expression.
  -/
  bvExpr : BVExpr width
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

def mkAtom (e : Expr) (width : Nat) : M ReifiedBVExpr := do
  let ident ← M.lookup e width
  let expr := mkApp2 (mkConst ``BVExpr.var) (toExpr width) (toExpr ident)
  let proof := do
    let evalExpr ← mkEvalExpr width expr
    return mkBVRefl width evalExpr
  return ⟨width, .var ident, proof, expr⟩

theorem and_congr (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs' &&& rhs' = lhs &&& rhs := by
  simp[*]

theorem or_congr (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs' ||| rhs' = lhs ||| rhs := by
  simp[*]

theorem xor_congr (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs' ^^^ rhs' = lhs ^^^ rhs := by
  simp[*]

theorem not_congr (x x' : BitVec w) (h : x = x') : ~~~x' = ~~~x := by
  simp[*]

theorem shiftLeft_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h : x = x') : x' <<< n = x <<< n := by
  simp[*]

theorem shiftRight_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h : x = x') : x' >>> n = x >>> n := by
  simp[*]

theorem add_congr (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs' + rhs' = lhs + rhs' := by
  simp[*]

theorem zeroExtend_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h1 : x = x') :
    BitVec.zeroExtend n x = BitVec.zeroExtend n x' := by
  simp[*]

def  getNatOrBvValue? (ty : Expr) (expr : Expr) : M (Option Nat) := do
  match_expr ty with
  | Nat =>
    getNatValue? expr
  | BitVec _ =>
    let some ⟨_, distance⟩ ← getBitVecValue? expr | return none
    return some distance.toNat
  | _ => return none

/--
Reify an `Expr` that's a `BitVec`.
-/
partial def of (x : Expr) : M (Option ReifiedBVExpr) := do
  match_expr x with
  | BitVec.ofNat _ _ => goBvLit x
  | OfNat.ofNat _ _ _ => goBvLit x
  | HAnd.hAnd _ _ _ _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .and ``and_congr
  | HOr.hOr _ _ _ _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .or ``or_congr
  | HXor.hXor _ _ _ _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .xor ``xor_congr
  | HAdd.hAdd _ _ _ _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .add ``add_congr
  | Complement.complement _ _ innerExpr =>
    let some inner ← of innerExpr | return none
    let bvExpr := .un .not inner.bvExpr
    let expr := mkApp3 (mkConst ``BVExpr.un) (toExpr inner.width) (mkConst ``BVUnOp.not) inner.expr
    let proof := unaryCongrProof inner innerExpr (mkConst ``not_congr)
    return some ⟨inner.width, bvExpr, proof, expr⟩
  | HShiftLeft.hShiftLeft _ β _ _ innerExpr distanceExpr =>
    shiftConstReflection
      β
      distanceExpr
      innerExpr
      .shiftLeftConst
      ``BVUnOp.shiftLeftConst
      ``shiftLeft_congr
  | HShiftRight.hShiftRight _ β _ _ innerExpr distanceExpr =>
    shiftConstReflection
      β
      distanceExpr
      innerExpr
      .shiftRightConst
      ``BVUnOp.shiftRightConst
      ``shiftRight_congr
  | BitVec.zeroExtend _ newWidthExpr innerExpr =>
    let some newWidth ← getNatValue? newWidthExpr | return ← ofAtom x
    let some inner ← of innerExpr | return none
    let bvExpr := .zeroExtend (w := inner.width) newWidth inner.bvExpr
    let expr :=
      mkApp3
        (mkConst ``BVExpr.zeroExtend)
        (toExpr inner.width)
        newWidthExpr
        inner.expr
    let proof := do
      let innerEval ← mkEvalExpr inner.width inner.expr
      let innerProof ← inner.evalsAtAtoms
      return mkApp5 (mkConst ``zeroExtend_congr) newWidthExpr (toExpr inner.width) innerExpr innerEval innerProof
    return some ⟨newWidth, bvExpr, proof, expr⟩
  | _ => ofAtom x
where
  ofAtom (x : Expr) : M (Option ReifiedBVExpr) := do
    let t ← instantiateMVars (← whnfR (← inferType x))
    let_expr BitVec widthExpr := t | return none
    let some width ← getNatValue? widthExpr | return none
    let atom ← mkAtom x width
    return some atom

  shiftConstReflection (β : Expr) (distanceExpr : Expr) (innerExpr : Expr)
        (shiftOp : Nat → BVUnOp) (shiftOpName : Name) (congrThm : Name)
        : M (Option ReifiedBVExpr) := do
    -- Either the shift values are constant or we abstract the entire term as atoms
    let some distance ← getNatOrBvValue? β distanceExpr | return ← ofAtom x
    let some inner ← of innerExpr | return none
    let bvExpr : BVExpr inner.width := .un (shiftOp distance) inner.bvExpr
    let expr :=
      mkApp3
        (mkConst ``BVExpr.un)
        (toExpr inner.width)
        (mkApp (mkConst shiftOpName) (toExpr distance))
        inner.expr
    let congrProof :=
      mkApp
        (mkConst congrThm)
        (toExpr distance)
    let proof := unaryCongrProof inner innerExpr congrProof
    return some ⟨inner.width, bvExpr, proof, expr⟩

  binaryReflection (lhsExpr rhsExpr : Expr) (op : BVBinOp) (congrThm : Name)
      : M (Option ReifiedBVExpr) := do
    let some lhs ← of lhsExpr | return none
    let some rhs ← of rhsExpr | return none
    if h : rhs.width = lhs.width then
      let bvExpr : BVExpr lhs.width := .bin lhs.bvExpr op (h ▸ rhs.bvExpr)
      let expr := mkApp4 (mkConst ``BVExpr.bin) (toExpr lhs.width) lhs.expr (toExpr op) rhs.expr
      let proof := binaryCongrProof lhs rhs lhsExpr rhsExpr congrThm
      return some ⟨lhs.width, bvExpr, proof, expr⟩
    else
      return none

  binaryCongrProof (lhs rhs : ReifiedBVExpr) (lhsExpr rhsExpr : Expr) (congrThm : Name) : M Expr := do
    let lhsEval ← mkEvalExpr lhs.width lhs.expr
    let lhsProof ← lhs.evalsAtAtoms
    let rhsProof ← rhs.evalsAtAtoms
    let rhsEval ← mkEvalExpr rhs.width rhs.expr
    return mkApp7 (mkConst congrThm) (toExpr lhs.width) lhsExpr rhsExpr lhsEval rhsEval lhsProof rhsProof

  unaryCongrProof (inner : ReifiedBVExpr) (innerExpr : Expr) (congrProof : Expr) : M Expr := do
    let innerEval ← mkEvalExpr inner.width inner.expr
    let innerProof ← inner.evalsAtAtoms
    return mkApp4 congrProof (toExpr inner.width) innerExpr innerEval innerProof

  goBvLit (x : Expr) : M (Option ReifiedBVExpr) := do
    let some ⟨width, bvVal⟩ ← getBitVecValue? x | return none
    let bvExpr : BVExpr width := .const bvVal
    let expr := mkApp2 (mkConst ``BVExpr.const) (toExpr width) (toExpr bvVal)
    let proof := do
      let evalExpr ← mkEvalExpr width expr
      return mkBVRefl width evalExpr
    return some ⟨width, bvExpr, proof, expr⟩

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
  A proof that `bvPred.eval atomsAssignment = originalBVPredExpr`.
  -/
  evalsAtAtoms : M Expr
  /--
  A cache for `toExpr bvPred`
  -/
  expr : Expr

namespace ReifiedBVPred

theorem beq_congr (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs)
    : (lhs == rhs) = (lhs' == rhs') := by
  simp[*]

def mkEvalExpr (expr : Expr) : M Expr := do
  return mkApp2 (mkConst ``BVPred.eval) (← M.atomsAssignment) expr

structure EqPair where
  fst : ReifiedBVExpr
  snd : ReifiedBVExpr
  heq : fst.width = snd.width

/--
Reify an `Expr` that is a proof of a predicate about `BitVec`.
-/
def of (t : Expr) : M (Option ReifiedBVPred) := do
  match_expr t with
  | BEq.beq α _ lhsExpr rhsExpr =>
    let_expr BitVec _ := α | return none
    let some lhs ← ReifiedBVExpr.of lhsExpr | return none
    let some rhs ← ReifiedBVExpr.of rhsExpr | return none
    if h:lhs.width = rhs.width then
      let bvExpr : BVPred := .bin (w := lhs.width) lhs.bvExpr .eq (h ▸ rhs.bvExpr)
      let expr :=
        mkApp4
          (mkConst ``BVPred.bin)
          (toExpr lhs.width)
          lhs.expr
          (mkConst ``BVBinPred.eq)
          rhs.expr
      let proof := do
        let lhsEval ← ReifiedBVExpr.mkEvalExpr lhs.width lhs.expr
        let lhsProof ← lhs.evalsAtAtoms
        let rhsEval ← ReifiedBVExpr.mkEvalExpr rhs.width rhs.expr
        let rhsProof ← rhs.evalsAtAtoms
        return mkApp7
          (mkConst ``beq_congr)
          (toExpr lhs.width)
          lhsExpr rhsExpr lhsEval rhsEval
          lhsProof
          rhsProof
      return some ⟨bvExpr, proof, expr⟩
    else
      return none
  | _ => return none

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
  A proof that `bvExpr.eval atomsAssignment = originalBVLoigcalExpr`.
  -/
  evalsAtAtoms : M Expr
  /--
  A cache for `toExpr bvExpr`
  -/
  expr : Expr


namespace ReifiedBVLogical

def mkRefl (expr : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) expr

def mkTrans (x y z : Expr) (hxy hyz : Expr) : Expr :=
  mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``Bool) x y z hxy hyz

def mkEvalExpr (expr : Expr) : M Expr := do
  return mkApp2 (mkConst ``BVLogicalExpr.eval) (← M.atomsAssignment) expr

theorem not_congr (x x' : Bool) (h : x = x') : (!x') = (!x) := by
  simp[*]

theorem and_congr (lhs rhs lhs' rhs' : Bool) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    (lhs' && rhs') = (lhs && rhs) := by
  simp[*]

theorem or_congr (lhs rhs lhs' rhs' : Bool) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    (lhs' || rhs') = (lhs || rhs') := by
  simp[*]

theorem xor_congr (lhs rhs lhs' rhs' : Bool) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    (xor lhs' rhs') = (xor lhs rhs) := by
  simp[*]

theorem beq_congr (lhs rhs lhs' rhs' : Bool) (h1 : lhs' = lhs) (h2 : rhs' = rhs)
    : (lhs == rhs) =  (lhs' == rhs') := by
  simp[*]

partial def of (t : Expr) : M (Option ReifiedBVLogical) := do
  trace[bv] m!"Reflecting into bvlogical: {t}"
  match_expr t with
  | Bool.true =>
    let boolExpr := .const true
    let expr := mkApp2 (mkConst ``BoolExpr.const) (mkConst ``BVPred) (toExpr Bool.true)
    let proof := return mkRefl (mkConst ``Bool.true)
    return some ⟨boolExpr, proof, expr⟩
  | Bool.false =>
    let boolExpr := .const false
    let expr := mkApp2 (mkConst ``BoolExpr.const) (mkConst ``BVPred) (toExpr Bool.false)
    let proof := return mkRefl (mkConst ``Bool.false)
    return some ⟨boolExpr, proof, expr⟩
  | not subExpr =>
    let some sub ← of subExpr | return none
    let boolExpr := .not sub.bvExpr
    let expr := mkApp2 (mkConst ``BoolExpr.not) (mkConst ``BVPred) sub.expr
    let proof := do
      let subEvalExpr ← mkEvalExpr sub.expr
      let subProof ← sub.evalsAtAtoms
      return mkApp3 (mkConst ``not_congr) subExpr subEvalExpr subProof
    return some ⟨boolExpr, proof, expr⟩
  | or lhsExpr rhsExpr => gateReflection lhsExpr rhsExpr .or ``or_congr
  | and lhsExpr rhsExpr => gateReflection lhsExpr rhsExpr .and ``and_congr
  | xor lhsExpr rhsExpr => gateReflection lhsExpr rhsExpr .xor ``xor_congr
  | BEq.beq α _ lhsExpr rhsExpr =>
    match_expr α with
    | Bool => gateReflection lhsExpr rhsExpr .beq ``beq_congr
    | BitVec _ => goPred t
    | _ => return none
  | _ => goPred t
where
  gateReflection (lhsExpr rhsExpr : Expr) (gate : Gate) (congrThm : Name) : M (Option ReifiedBVLogical) := do
    let some lhs ← of lhsExpr | return none
    let some rhs ← of rhsExpr | return none
    let boolExpr := .gate  gate lhs.bvExpr rhs.bvExpr
    let expr :=
      mkApp4
        (mkConst ``BoolExpr.gate)
        (mkConst ``BVPred)
        (toExpr gate)
        lhs.expr
        rhs.expr
    let proof := do
      let lhsEvalExpr ← mkEvalExpr lhs.expr
      let rhsEvalExpr ← mkEvalExpr rhs.expr
      let lhsProof ← lhs.evalsAtAtoms
      let rhsProof ← rhs.evalsAtAtoms
      return mkApp6
        (mkConst congrThm)
        lhsExpr rhsExpr
        lhsEvalExpr rhsEvalExpr
        lhsProof rhsProof
    return some ⟨boolExpr, proof, expr⟩

  goPred (t : Expr) : M (Option ReifiedBVLogical) := do
    trace[bv] m!"referring to pred: {t}"
    let some bvPred ← ReifiedBVPred.of t | return none
    trace[bv] m!"pred succesful!"
    let boolExpr := .literal bvPred.bvPred
    let expr := mkApp2 (mkConst ``BoolExpr.literal) (mkConst ``BVPred) bvPred.expr
    let proof := bvPred.evalsAtAtoms
    return some ⟨boolExpr, proof, expr⟩

end ReifiedBVLogical

/--
A reified version of an `Expr` representing a `BVLogicalExpr` that we know to be true.
-/
structure SatAtBVLogical where
  /--
  The reified expression.
  -/
  bvExpr : BVLogicalExpr
  /--
  A proof that `bvExpr.eval atomsAssignment = true`.
  -/
  satAtAtoms : M Expr
  /--
  A cache for `toExpr bvExpr`
  -/
  expr : Expr

namespace SatAtBVLogical

/--
Reify an `Expr` that is a proof of some boolean structure on top of predicates about `BitVec`s.
-/
partial def of (h : Expr) : M (Option SatAtBVLogical) := do
  let t ← instantiateMVars (← whnfR (← inferType h))
  match_expr t with
  | Eq α lhsExpr rhsExpr =>
    let_expr Bool := α | return none
    let_expr Bool.true := rhsExpr | return none
    trace[bv] m!"Did not filter hypothesis of type: {t}"
    -- We now know that `h : lhsExpr = true`
    -- We attempt to reify lhsExpr into a BVLogicalExpr, then prove that evaluating
    -- this BVLogicalExpr must eval to true due to `h`
    let some bvLogical ← ReifiedBVLogical.of lhsExpr | return none
    let proof := do
      -- call this eval term x
      let evalLogic ← ReifiedBVLogical.mkEvalExpr bvLogical.expr
      -- this is x = lhsExpr
      let evalProof ← bvLogical.evalsAtAtoms
      -- h is lhsExpr = true
      -- we prove lhsExpr = true by lhsExpr = y = true
      return ReifiedBVLogical.mkTrans lhsExpr evalLogic (mkConst ``Bool.true) evalProof h
    return some ⟨bvLogical.bvExpr, proof, bvLogical.expr⟩
  | _ => return none

/--
The trivially true `BVLogicalExpr`.
-/
def trivial : SatAtBVLogical where
  bvExpr := .const true
  expr := toExpr (.const true : BVLogicalExpr)
  satAtAtoms := return mkApp (mkConst ``BVLogicalExpr.sat_true) (← M.atomsAssignment)

/--
Logical conjunction of two `ReifiedBVLogical`.
-/
def and (x y : SatAtBVLogical) : SatAtBVLogical where
  bvExpr := .gate .and x.bvExpr y.bvExpr
  expr := mkApp4 (mkConst ``BoolExpr.gate) (mkConst ``BVPred) (mkConst ``Gate.and) x.expr y.expr
  satAtAtoms :=
    return mkApp5
      (mkConst ``BVLogicalExpr.sat_and)
      x.expr
      y.expr
      (← M.atomsAssignment)
      (← x.satAtAtoms)
      (← y.satAtAtoms)

/-- Given a proof that `x.expr.unsat`, produce a proof of `False`. -/
def proveFalse (x : SatAtBVLogical) (h : Expr) : M Expr := do
  let atomsList ← M.atomsAssignment
  let evalExpr := mkApp2 (mkConst ``BVLogicalExpr.eval) atomsList x.expr
  return mkApp3
    (mkConst ``ReflectSat.SatAtAtoms.false_of_eq_true_of_eq_false)
    evalExpr
    (← x.satAtAtoms)
    (.app h atomsList)


end SatAtBVLogical

/--
Given a goal `g`, which should be `False`, returns
* a `e : BVLogicalExpr` (representing the conjunction of all bitvec predicates in hypotheses of `g`)
* a function which takes an expression representing a proof of `e.unsat`,
  and returns a proof of `False` valid in the context of `g`.
-/
def verifyBVExpr (bv : BVLogicalExpr) (cert : SatDecide.LratCert) : Bool :=
  SatDecide.verifyCert (SatDecide.LratFormula.ofCnf (AIG.toCNF bv.bitblast.relabelNat)) cert

theorem unsat_of_verifyBVExpr_eq_true (bv : BVLogicalExpr) (c : SatDecide.LratCert)
    (h : verifyBVExpr bv c = true) : bv.unsat := by
  apply BVLogicalExpr.unsat_of_bitblast
  rw [← AIG.Entrypoint.relabelNat_unsat_iff]
  rw [← AIG.toCNF_equisat]
  apply SatDecide.verifyCert_correct
  rw [verifyBVExpr] at h
  assumption

def lratBitblaster (cfg : SatDecide.TacticContext) (bv : BVLogicalExpr) : MetaM Expr := do
  let entry ←
    withTraceNode `bv (fun _ => return "Bitblasting BVLogicalExpr to AIG") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ => bv.bitblast)
  trace[bv] s!"AIG has {entry.aig.decls.size} nodes."

  let cnf ←
    withTraceNode `sat (fun _ => return "Converting AIG to CNF") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ => AIG.toCNF (entry.relabelNat))

  let encoded ←
    withTraceNode `sat (fun _ => return "Converting frontend CNF to solver specific CNF") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ => SatDecide.LratFormula.ofCnf cnf)
  trace[sat] s!"CNF has {encoded.formula.clauses.size} clauses"

  let cert ←
    withTraceNode `sat (fun _ => return "Obtaining external proof certificate") do
      SatDecide.runExternal encoded cfg.solver cfg.lratPath cfg.prevalidate

  cert.toReflectionProof cfg bv ``verifyBVExpr ``unsat_of_verifyBVExpr_eq_true

def reflectBV (g : MVarId) : M (BVLogicalExpr × (Expr → M Expr)) := g.withContext do
  let hyps ← getLocalHyps
  let sats ← hyps.filterMapM SatAtBVLogical.of
  let sat := sats.foldl (init := SatAtBVLogical.trivial) SatAtBVLogical.and
  return (sat.bvExpr, sat.proveFalse)

def _root_.Lean.MVarId.closeWithBVReflection (g : MVarId) (unsatProver : BVLogicalExpr → MetaM Expr) : MetaM Unit := M.run do
  g.withContext do
    let (bvLogicalExpr, f) ←
      withTraceNode `bv (fun _ => return "Reflecting goal into BVLogicalExpr") do
        reflectBV g
    trace[bv] "Reflected bv logical expression: {bvLogicalExpr}"

    let bvExprUnsat ← unsatProver bvLogicalExpr
    let proveFalse ← f bvExprUnsat
    g.assign proveFalse

syntax (name := bvUnsatSyntax) "bv_unsat" : tactic

def _root_.Lean.MVarId.bvUnsat (g : MVarId) (cfg : SatDecide.TacticContext) : MetaM Unit := M.run do
  let unsatProver (exp : BVLogicalExpr) : MetaM Expr := do
    withTraceNode `bv (fun _ => return "Preparing LRAT reflection term") do
      lratBitblaster cfg exp
  g.closeWithBVReflection unsatProver

open Elab.Tactic
elab_rules : tactic
  | `(tactic| bv_unsat) => do
    let cfg ← SatDecide.TacticContext.new (← SatDecide.mkTemp)
    liftMetaFinishingTactic fun g => g.bvUnsat cfg

/-
Close a goal by:
1. Turning it into a BitVec problem.
2. Using bitblasting to turn that into a SAT problem.
3. Running an external SAT solver on it and obtaining an LRAT proof from it.
4. Verifying the LRAT proof using proof by reflection.
-/
syntax (name := bvDecideSyntax) "bv_decide" : tactic

end BVDecide

macro_rules
| `(tactic| bv_decide) =>
  `(tactic| bv_normalize <;> bv_unsat)
