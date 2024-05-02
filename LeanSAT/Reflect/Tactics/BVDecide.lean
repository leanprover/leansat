/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.Reflect.BVExpr.BitBlast
import LeanSAT.Reflect.Tactics.SatDecide

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

def mkAtom (e : Expr) (width : Nat) : M (ReifiedBVExpr width) := do
  let ident ← M.lookup e width
  let expr := mkApp2 (mkConst ``BVExpr.var) (toExpr width) (toExpr ident)
  let proof := do
    let evalExpr ← mkEvalExpr width expr
    return mkBVRefl width evalExpr
  return ⟨.var ident, proof, expr⟩

theorem and_congr (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs' &&& rhs' = lhs &&& rhs' := by
  simp[*]

theorem or_congr (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs' ||| rhs' = lhs ||| rhs' := by
  simp[*]

theorem xor_congr (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs' ^^^ rhs' = lhs ^^^ rhs' := by
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
partial def of {w : Nat} (x : Expr) : M (Option (ReifiedBVExpr w)) := do
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
    let bvExpr : BVExpr w := .un .not inner.bvExpr
    let expr := mkApp3 (mkConst ``BVExpr.un) (toExpr w) (mkConst ``BVUnOp.not) inner.expr
    let proof := unaryCongrProof inner innerExpr (mkConst ``not_congr)
    return some ⟨bvExpr, proof, expr⟩
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
  | _ => ofAtom x
where
  ofAtom {w : Nat} (x : Expr) : M (Option (ReifiedBVExpr w)) := do
    let t ← instantiateMVars (← whnfR (← inferType x))
    let_expr BitVec widthExpr := t | return none
    let some width ← getNatValue? widthExpr | return none
    if h:width = w then
      h ▸ mkAtom x width
    else
      panic! "Attempt to reify ill-typed BitVec value"

  shiftConstReflection {w : Nat} (β : Expr) (distanceExpr : Expr) (innerExpr : Expr)
        (shiftOp : Nat → BVUnOp) (shiftOpName : Name) (congrThm : Name)
        : M (Option (ReifiedBVExpr w)) := do
    -- Either the shift values are constant or we abstract the entire term as atoms
    let some distance ← getNatOrBvValue? β distanceExpr | return ← ofAtom x
    let some inner ← of innerExpr | return none
    let bvExpr : BVExpr w := .un (shiftOp distance) inner.bvExpr
    let expr :=
      mkApp3
        (mkConst ``BVExpr.un)
        (toExpr w)
        (mkApp (mkConst shiftOpName) (toExpr distance))
        inner.expr
    let congrProof :=
      mkApp
        (mkConst congrThm)
        (toExpr distance)
    let proof := unaryCongrProof inner innerExpr congrProof
    return some ⟨bvExpr, proof, expr⟩

  binaryReflection {w : Nat} (lhsExpr rhsExpr : Expr) (op : BVBinOp) (congrThm : Name)
      : M (Option (ReifiedBVExpr w)) := do
    let some lhs ← of lhsExpr | return none
    let some rhs ← of rhsExpr | return none
    let bvExpr := .bin lhs.bvExpr op rhs.bvExpr
    let expr := mkApp4 (mkConst ``BVExpr.bin) (toExpr w) lhs.expr (toExpr op) rhs.expr
    let proof := binaryCongrProof lhs rhs lhsExpr rhsExpr congrThm
    return some ⟨bvExpr, proof, expr⟩

  binaryCongrProof {w : Nat} (lhs rhs : ReifiedBVExpr w) (lhsExpr rhsExpr : Expr) (congrThm : Name) : M Expr := do
    let lhsEval ← mkEvalExpr w lhs.expr
    let lhsProof ← lhs.evalsAtAtoms
    let rhsProof ← rhs.evalsAtAtoms
    let rhsEval ← mkEvalExpr w rhs.expr
    return mkApp7 (mkConst congrThm) (toExpr w) lhsExpr rhsExpr lhsEval rhsEval lhsProof rhsProof

  unaryCongrProof {w : Nat} (inner : ReifiedBVExpr w) (innerExpr : Expr) (congrProof : Expr) : M Expr := do
    let innerEval ← mkEvalExpr w inner.expr
    let innerProof ← inner.evalsAtAtoms
    return mkApp4 congrProof (toExpr w) innerExpr innerEval innerProof

  goBvLit {w : Nat} (x : Expr) : M (Option (ReifiedBVExpr w)) := do
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


def mkEvalExpr (expr : Expr) : M Expr := do
  return mkApp2 (mkConst ``BVPred.eval) (← M.atomsAssignment) expr

/--
Reify an `Expr` that is a proof of a predicate about `BitVec`.
-/
def of (h : Expr) : M (Option ReifiedBVPred) := do
  let t ← instantiateMVars (← whnfR (← inferType h))
  match_expr t with
  -- TODO: support negations other than equality
  | Not w =>
    match_expr w with
    | Eq α lhsExpr rhsExpr =>
      let_expr BitVec widthExpr := α | return none
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
  | Eq α lhsExpr rhsExpr =>
    let_expr BitVec widthExpr := α | return none
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

def mkEvalExpr (expr : Expr) : M Expr := do
  return mkApp2 (mkConst ``BVLogicalExpr.eval) (← M.atomsAssignment) expr

/--
Reify an `Expr` that is a proof of some boolean structure on top of predicates about `BitVec`s.
-/
partial def of (h : Expr) : M (Option ReifiedBVLogical) := do
  -- TODO: naive approach, does not handle any boolean structure on top of our problem.
  let t ← instantiateMVars (← whnfR (← inferType h))
  match_expr t with
  | Not w =>
    -- TODO: support negations other than equality on BitVec
    match_expr w with
    | Eq α _ _ =>
      let_expr BitVec _ := α | return none
      goPred h
    | _ => return none
  | _ => goPred h
where
  goPred (h : Expr) : M (Option ReifiedBVLogical) := do
    let some pred ← ReifiedBVPred.of h | return none
    let bvExpr := .literal pred.bvPred
    let expr := mkApp2 (mkConst ``BoolExpr.literal) (mkConst ``BVPred) pred.expr
    let proof := do
      let evalLogic ← mkEvalExpr expr
      let evalPred ← ReifiedBVPred.mkEvalExpr pred.expr
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
  let sats ← hyps.filterMapM ReifiedBVLogical.of
  let sat := sats.foldl (init := ReifiedBVLogical.trivial) ReifiedBVLogical.and
  return (sat.bvExpr, sat.proveFalse)

def _root_.Lean.MVarId.closeWithBVReflection (g : MVarId) (unsatProver : BVLogicalExpr → MetaM Expr) : MetaM Unit := M.run do
  let g' ← g.falseOrByContra
  g'.withContext do
    let (bvLogicalExpr, f) ←
      withTraceNode `bv (fun _ => return "Reflecting goal into BVLogicalExpr") do
        reflectBV g'
    trace[bv] "Reflected bv logical expression: {bvLogicalExpr}"

    let bvExprUnsat ← unsatProver bvLogicalExpr
    let proveFalse ← f bvExprUnsat
    g'.assign proveFalse

/--
Close a goal by:
1. Turning it into a BitVec problem.
2. Using bitblasting to turn that into a SAT problem.
3. Running an external SAT solver on it and obtaining an LRAT proof from it.
4. Verifying the LRAT proof using proof by reflection.
-/
def _root_.Lean.MVarId.bvDecide (g : MVarId) (cfg : SatDecide.TacticContext) : MetaM Unit := M.run do
  let unsatProver (exp : BVLogicalExpr) : MetaM Expr := do
    withTraceNode `bv (fun _ => return "Preparing LRAT reflection term") do
      lratBitblaster cfg exp
  g.closeWithBVReflection unsatProver

@[inherit_doc _root_.Lean.MVarId.bvDecide]
syntax (name := bvDecideSyntax) "bv_decide" : tactic

end BVDecide

open Elab.Tactic
elab_rules : tactic
  | `(tactic| bv_decide) => do
    let cfg ← SatDecide.TacticContext.new (← SatDecide.mkTemp)
    liftMetaFinishingTactic fun g => g.bvDecide cfg
