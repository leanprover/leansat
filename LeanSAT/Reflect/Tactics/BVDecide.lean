/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.BVExpr.BitBlast
import LeanSAT.Reflect.Tactics.Normalize
import LeanSAT.Reflect.LRAT
import LeanSAT.AIG.CNF
import LeanSAT.AIG.RelabelNat

open Lean Meta

namespace BVDecide

structure UnsatProver.Result where
  proof : Expr
  lratCert : LratCert

abbrev UnsatProver := BVLogicalExpr → Batteries.HashMap Nat Expr → MetaM UnsatProver.Result

-- TODO: This should be upstream?
instance : ToExpr (BitVec w) where
  toExpr bv := mkApp2 (mkConst ``BitVec.ofNat) (toExpr w) (toExpr bv.toNat)
  toTypeExpr := mkApp (mkConst ``BitVec) (toExpr w)

instance : ToExpr BVBinPred where
  toExpr x :=
    match x with
    | .eq => mkConst ``BVBinPred.eq
    | .ult => mkConst ``BVBinPred.ult
  toTypeExpr := mkConst ``BVBinPred

instance : ToExpr BVUnOp where
  toExpr x :=
    match x with
    | .not => mkConst ``BVUnOp.not
    | .shiftLeftConst n => mkApp (mkConst ``BVUnOp.shiftLeftConst) (toExpr n)
    | .shiftRightConst n => mkApp (mkConst ``BVUnOp.shiftRightConst) (toExpr n)
    | .rotateLeft n => mkApp (mkConst ``BVUnOp.rotateLeft) (toExpr n)
    | .rotateRight n => mkApp (mkConst ``BVUnOp.rotateRight) (toExpr n)
    | .arithShiftRightConst n => mkApp (mkConst ``BVUnOp.arithShiftRightConst) (toExpr n)
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
  | .signExtend (w := oldWidth) val inner =>
    mkApp3 (mkConst ``BVExpr.signExtend) (toExpr oldWidth) (toExpr val) (go inner)
  | .bin lhs op rhs => mkApp4 (mkConst ``BVExpr.bin) (toExpr w) (go lhs) (toExpr op) (go rhs)
  | .un op operand => mkApp3 (mkConst ``BVExpr.un) (toExpr w) (toExpr op) (go operand)
  | .append (l := l) (r := r) lhs rhs =>
    mkApp4 (mkConst ``BVExpr.append) (toExpr l) (toExpr r) (go lhs) (go rhs)
  | .extract (w := oldWidth) hi lo expr =>
    mkApp4 (mkConst ``BVExpr.extract) (toExpr oldWidth) (toExpr hi) (toExpr lo) (go expr)

instance : ToExpr BVPred where
  toExpr x := go x
  toTypeExpr := mkConst ``BVPred
where
  go : BVPred → Expr
  | .bin (w := w) lhs op rhs =>
    mkApp4 (mkConst ``BVPred.bin) (toExpr w) (toExpr lhs) (toExpr op) (toExpr rhs)
  | .getLsb (w := w) expr idx =>
    mkApp3 (mkConst ``BVPred.getLsb) (toExpr w) (toExpr expr) (toExpr idx)

instance : ToExpr Gate where
  toExpr x :=
    match x with
    | .and => mkConst ``Gate.and
    | .or => mkConst ``Gate.or
    | .xor => mkConst ``Gate.xor
    | .imp => mkConst ``Gate.imp
    | .beq => mkConst ``Gate.beq
  toTypeExpr := mkConst ``Gate

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

theorem and_congr (w : Nat) (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs' &&& rhs' = lhs &&& rhs := by
  simp[*]

theorem or_congr (w : Nat) (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs' ||| rhs' = lhs ||| rhs := by
  simp[*]

theorem xor_congr (w : Nat) (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs' ^^^ rhs' = lhs ^^^ rhs := by
  simp[*]

theorem not_congr (w : Nat) (x x' : BitVec w) (h : x = x') : ~~~x' = ~~~x := by
  simp[*]

theorem shiftLeft_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h : x = x')
    : x' <<< n = x <<< n := by
  simp[*]

theorem shiftRight_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h : x = x')
    : x' >>> n = x >>> n := by
  simp[*]

theorem arithShiftRight_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h : x = x')
    : BitVec.sshiftRight x' n = BitVec.sshiftRight x n := by
  simp[*]

theorem add_congr (w : Nat) (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs' + rhs' = lhs + rhs := by
  simp[*]

theorem zeroExtend_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h1 : x = x') :
    BitVec.zeroExtend n x' = BitVec.zeroExtend n x := by
  simp[*]

theorem signExtend_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h1 : x = x') :
    BitVec.signExtend n x' = BitVec.signExtend n x := by
  simp[*]

theorem append_congr (lw rw : Nat) (lhs lhs' : BitVec lw) (rhs rhs' : BitVec rw) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs' ++ rhs' = lhs ++ rhs := by
  simp[*]

theorem extract_congr (hi lo : Nat) (w : Nat) (x x' : BitVec w) (h1 : x = x') :
    BitVec.extractLsb hi lo x' = BitVec.extractLsb hi lo x := by
  simp[*]

theorem rotateLeft_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h : x = x')
    : BitVec.rotateLeft x' n = BitVec.rotateLeft x n := by
  simp[*]

theorem rotateRight_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h : x = x')
    : BitVec.rotateRight x' n = BitVec.rotateRight x n := by
  simp[*]

def getNatOrBvValue? (ty : Expr) (expr : Expr) : M (Option Nat) := do
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
  | BitVec.ofNatLt _ _ _ => goBvLit x
  | HAnd.hAnd _ _ _ _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .and ``and_congr
  | HOr.hOr _ _ _ _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .or ``or_congr
  | HXor.hXor _ _ _ _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .xor ``xor_congr
  | HAdd.hAdd _ _ _ _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .add ``add_congr
  | Complement.complement _ _ innerExpr =>
    unaryReflection innerExpr .not ``not_congr
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
  | BitVec.sshiftRight _ innerExpr distanceExpr =>
    let some distance ← getNatValue? distanceExpr | return ← ofAtom x
    shiftLikeReflection
      distance
      innerExpr
      .arithShiftRightConst
      ``BVUnOp.arithShiftRightConst
      ``arithShiftRight_congr
  | BitVec.zeroExtend _ newWidthExpr innerExpr =>
    let some newWidth ← getNatValue? newWidthExpr | return ← ofAtom x
    let some inner ← of innerExpr | return none
    let bvExpr := .zeroExtend newWidth inner.bvExpr
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
  | BitVec.signExtend _ newWidthExpr innerExpr =>
    let some newWidth ← getNatValue? newWidthExpr | return ← ofAtom x
    let some inner ← of innerExpr | return none
    let bvExpr := .signExtend newWidth inner.bvExpr
    let expr :=
      mkApp3
        (mkConst ``BVExpr.signExtend)
        (toExpr inner.width)
        newWidthExpr
        inner.expr
    let proof := do
      let innerEval ← mkEvalExpr inner.width inner.expr
      let innerProof ← inner.evalsAtAtoms
      return mkApp5 (mkConst ``signExtend_congr) newWidthExpr (toExpr inner.width) innerExpr innerEval innerProof
    return some ⟨newWidth, bvExpr, proof, expr⟩
  | HAppend.hAppend _ _ _ _ lhsExpr rhsExpr =>
    let some lhs ← of lhsExpr | return none
    let some rhs ← of rhsExpr | return none
    let bvExpr := .append lhs.bvExpr rhs.bvExpr
    let expr := mkApp4 (mkConst ``BVExpr.append) (toExpr lhs.width) (toExpr rhs.width) lhs.expr rhs.expr
    let proof := do
      let lhsEval ← mkEvalExpr lhs.width lhs.expr
      let lhsProof ← lhs.evalsAtAtoms
      let rhsProof ← rhs.evalsAtAtoms
      let rhsEval ← mkEvalExpr rhs.width rhs.expr
      return mkApp8 (mkConst ``append_congr)
        (toExpr lhs.width) (toExpr rhs.width)
        lhsExpr lhsEval
        rhsExpr rhsEval
        lhsProof rhsProof
    return some ⟨lhs.width + rhs.width, bvExpr, proof, expr⟩
  | BitVec.extractLsb _ hiExpr loExpr innerExpr =>
    let some hi ← getNatValue? hiExpr | return none
    let some lo ← getNatValue? loExpr | return none
    let some inner ← of innerExpr | return none
    let bvExpr := .extract hi lo inner.bvExpr
    let expr := mkApp4 (mkConst ``BVExpr.extract)
      (toExpr inner.width)
      hiExpr
      loExpr
      inner.expr
    let proof := do
      let innerEval ← mkEvalExpr inner.width inner.expr
      let innerProof ← inner.evalsAtAtoms
      return mkApp6 (mkConst ``extract_congr)
        hiExpr
        loExpr
        (toExpr inner.width)
        innerExpr
        innerEval
        innerProof
    return some ⟨hi - lo + 1, bvExpr, proof, expr⟩
  | BitVec.rotateLeft _ innerExpr distanceExpr =>
    rotateReflection
      distanceExpr
      innerExpr
      .rotateLeft
      ``BVUnOp.rotateLeft
      ``rotateLeft_congr
  | BitVec.rotateRight _ innerExpr distanceExpr =>
    rotateReflection
      distanceExpr
      innerExpr
      .rotateRight
      ``BVUnOp.rotateRight
      ``rotateRight_congr
  | _ => ofAtom x
where
  ofAtom (x : Expr) : M (Option ReifiedBVExpr) := do
    let t ← instantiateMVars (← whnfR (← inferType x))
    let_expr BitVec widthExpr := t | return none
    let some width ← getNatValue? widthExpr | return none
    let atom ← mkAtom x width
    return some atom

  shiftLikeReflection (distance : Nat) (innerExpr : Expr) (shiftOp : Nat → BVUnOp)
      (shiftOpName : Name) (congrThm : Name)
      : M (Option ReifiedBVExpr) := do
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

  rotateReflection (distanceExpr : Expr) (innerExpr : Expr)
        (rotateOp : Nat → BVUnOp) (rotateOpName : Name) (congrThm : Name)
        : M (Option ReifiedBVExpr) := do
    -- Either the shift values are constant or we abstract the entire term as atoms
    let some distance ← getNatValue? distanceExpr | return ← ofAtom x
    shiftLikeReflection distance innerExpr rotateOp rotateOpName congrThm

  shiftConstReflection (β : Expr) (distanceExpr : Expr) (innerExpr : Expr)
        (shiftOp : Nat → BVUnOp) (shiftOpName : Name) (congrThm : Name)
        : M (Option ReifiedBVExpr) := do
    -- Either the shift values are constant or we abstract the entire term as atoms
    let some distance ← getNatOrBvValue? β distanceExpr | return ← ofAtom x
    shiftLikeReflection distance innerExpr shiftOp shiftOpName congrThm

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

  unaryReflection (innerExpr : Expr) (op : BVUnOp) (congrThm : Name) : M (Option ReifiedBVExpr) := do
    let some inner ← of innerExpr | return none
    let bvExpr := .un op inner.bvExpr
    let expr := mkApp3 (mkConst ``BVExpr.un) (toExpr inner.width) (toExpr op) inner.expr
    let proof := unaryCongrProof inner innerExpr (mkConst congrThm)
    return some ⟨inner.width, bvExpr, proof, expr⟩

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
    : (lhs' == rhs') = (lhs == rhs) := by
  simp[*]

theorem ult_congr (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs)
    : (BitVec.ult lhs' rhs') = (BitVec.ult lhs rhs) := by
  simp[*]

theorem getLsb_congr (i : Nat) (w : Nat) (e e' : BitVec w) (h : e' = e)
    : (e'.getLsb i) = (e.getLsb i) := by
  simp[*]

theorem ofBool_congr (b : Bool) (e' : BitVec 1) (h : e' = BitVec.ofBool b) : e'.getLsb 0 = b := by
  cases b <;> simp [h]

/--
Reify an `Expr` that is a proof of a predicate about `BitVec`.
-/
def of (t : Expr) : M (Option ReifiedBVPred) := do
  match_expr t with
  | BEq.beq α _ lhsExpr rhsExpr =>
    let_expr BitVec _ := α | return none
    binaryReflection lhsExpr rhsExpr .eq ``beq_congr
  | BitVec.ult _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .ult ``ult_congr
  | BitVec.getLsb _ subExpr idxExpr =>
    let some sub ← ReifiedBVExpr.of subExpr | return none
    let some idx ← getNatValue? idxExpr | return none
    let bvExpr : BVPred := .getLsb sub.bvExpr idx
    let expr := mkApp3 (mkConst ``BVPred.getLsb) (toExpr sub.width) sub.expr idxExpr
    let proof := do
      let subEval ← ReifiedBVExpr.mkEvalExpr sub.width sub.expr
      let subProof ← sub.evalsAtAtoms
      return mkApp5
        (mkConst ``getLsb_congr)
        idxExpr
        (toExpr sub.width)
        subExpr
        subEval
        subProof
    return some ⟨bvExpr, proof, expr⟩
  | _ =>
    /-
    Idea: we have t : Bool here, let's construct:
      BitVec.ofBool t : BitVec 1
    as an atom. Then construct the BVPred corresponding to
      BitVec.getLsb (BitVec.ofBool t) 0 : Bool
    We can prove that this is equivalent to `t`. This allows us to have boolean variables in BVPred.
    -/
    let ty ← inferType t
    let_expr Bool := ty | return none
    let atom ← ReifiedBVExpr.mkAtom (mkApp (mkConst ``BitVec.ofBool) t) 1
    let bvExpr : BVPred := .getLsb atom.bvExpr 0
    let expr := mkApp3 (mkConst ``BVPred.getLsb) (toExpr 1) atom.expr (toExpr 0)
    let proof := do
      let atomEval ← ReifiedBVExpr.mkEvalExpr atom.width atom.expr
      let atomProof ← atom.evalsAtAtoms
      return mkApp3
        (mkConst ``ofBool_congr)
        t
        atomEval
        atomProof
    return some ⟨bvExpr, proof, expr⟩
where
  binaryReflection (lhsExpr rhsExpr : Expr) (pred : BVBinPred) (congrThm : Name)
      : M (Option ReifiedBVPred) := do
    let some lhs ← ReifiedBVExpr.of lhsExpr | return none
    let some rhs ← ReifiedBVExpr.of rhsExpr | return none
    if h:lhs.width = rhs.width then
      let bvExpr : BVPred := .bin (w := lhs.width) lhs.bvExpr pred (h ▸ rhs.bvExpr)
      let expr :=
        mkApp4
          (mkConst ``BVPred.bin)
          (toExpr lhs.width)
          lhs.expr
          (toExpr pred)
          rhs.expr
      let proof := do
        let lhsEval ← ReifiedBVExpr.mkEvalExpr lhs.width lhs.expr
        let lhsProof ← lhs.evalsAtAtoms
        let rhsEval ← ReifiedBVExpr.mkEvalExpr rhs.width rhs.expr
        let rhsProof ← rhs.evalsAtAtoms
        return mkApp7
          (mkConst congrThm)
          (toExpr lhs.width)
          lhsExpr rhsExpr lhsEval rhsEval
          lhsProof
          rhsProof
      return some ⟨bvExpr, proof, expr⟩
    else
      return none


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

theorem not_congr (x x' : Bool) (h : x' = x) : (!x') = (!x) := by
  simp[*]

theorem and_congr (lhs rhs lhs' rhs' : Bool) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    (lhs' && rhs') = (lhs && rhs) := by
  simp[*]

theorem or_congr (lhs rhs lhs' rhs' : Bool) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    (lhs' || rhs') = (lhs || rhs) := by
  simp[*]

theorem xor_congr (lhs rhs lhs' rhs' : Bool) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    (xor lhs' rhs') = (xor lhs rhs) := by
  simp[*]

theorem beq_congr (lhs rhs lhs' rhs' : Bool) (h1 : lhs' = lhs) (h2 : rhs' = rhs)
    : (lhs' == rhs') = (lhs == rhs) := by
  simp[*]

partial def of (t : Expr) : M (Option ReifiedBVLogical) := do
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
    let some bvPred ← ReifiedBVPred.of t | return none
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
    -- We now know that `h : lhsExpr = true`
    -- We attempt to reify lhsExpr into a BVLogicalExpr, then prove that evaluating
    -- this BVLogicalExpr must eval to true due to `h`
    let some bvLogical ← ReifiedBVLogical.of lhsExpr | return none
    let proof := do
      let evalLogic ← ReifiedBVLogical.mkEvalExpr bvLogical.expr
      -- this is evalLogic = lhsExpr
      let evalProof ← bvLogical.evalsAtAtoms
      -- h is lhsExpr = true
      -- we prove evalLogic = true by evalLogic = lhsExpr = true
      return ReifiedBVLogical.mkTrans evalLogic lhsExpr (mkConst ``Bool.true) evalProof h
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

theorem false_of_eq_true_of_eq_false (h₁ : x = true) (h₂ : x = false) : False := by
  cases h₁; cases h₂

/-- Given a proof that `x.expr.unsat`, produce a proof of `False`. -/
def proveFalse (x : SatAtBVLogical) (h : Expr) : M Expr := do
  let atomsList ← M.atomsAssignment
  let evalExpr := mkApp2 (mkConst ``BVLogicalExpr.eval) atomsList x.expr
  return mkApp3
    (mkConst ``false_of_eq_true_of_eq_false)
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
def verifyBVExpr (bv : BVLogicalExpr) (cert : LratCert) : Bool :=
  verifyCert (LratFormula.ofCnf (AIG.toCNF bv.bitblast.relabelNat)) cert

theorem unsat_of_verifyBVExpr_eq_true (bv : BVLogicalExpr) (c : LratCert)
    (h : verifyBVExpr bv c = true) : bv.unsat := by
  apply BVLogicalExpr.unsat_of_bitblast
  rw [← AIG.Entrypoint.relabelNat_unsat_iff]
  rw [← AIG.toCNF_equisat]
  apply verifyCert_correct
  rw [verifyBVExpr] at h
  assumption

def reconstructCounterExample (var2Cnf : Batteries.HashMap BVBit Nat) (assignment : Array (Bool × Nat))
    (aigSize : Nat) (atomsAssignment : Batteries.HashMap Nat Expr) : Array (Expr × BVExpr.PackedBitVec) := Id.run do
  let mut sparseMap : Batteries.HashMap Nat (RBMap Nat Bool Ord.compare) := {}
  for (bitVar, cnfVar) in var2Cnf.toArray do
    /-
    The setup of the variables in CNF is as follows:
    1. One auxiliary variable for each node in the AIG
    2. The actual BitVec bitwise variables
    Hence we access the assignment array offset by the AIG size to obtain the value for a BitVec bit.
    -/
    -- We assume that a variable can be found at its index (off by one) as CaDiCal prints them in order.
    let (varSet, cnfVar') := assignment[cnfVar + aigSize]!
    -- But we are also paranoid. Off by one because internal count starts at 0 but CNF starts at 1.
    assert! cnfVar' == (cnfVar + aigSize + 1)
    let mut bitMap := sparseMap.find? bitVar.var |>.getD {}
    bitMap := bitMap.insert bitVar.idx varSet
    sparseMap := sparseMap.insert bitVar.var bitMap

  let mut finalMap := #[]
  for (bitVecVar, bitMap) in sparseMap.toArray do
    let mut value : Nat := 0
    let mut currentBit := 0
    for (bitIdx, bitValue) in bitMap.toList do
      assert! bitIdx == currentBit
      if bitValue then
        value := value ||| (1 <<< currentBit)
      currentBit := currentBit + 1
    let atomExpr := atomsAssignment.find! bitVecVar
    finalMap := finalMap.push (atomExpr, ⟨BitVec.ofNat currentBit value⟩)
  return finalMap

def lratBitblaster (cfg : TacticContext) (bv : BVLogicalExpr)
    (atomsAssignment : Batteries.HashMap Nat Expr) : MetaM UnsatProver.Result := do
  let entry ←
    withTraceNode `bv (fun _ => return "Bitblasting BVLogicalExpr to AIG") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ => bv.bitblast)
  let aigSize := entry.aig.decls.size
  trace[bv] s!"AIG has {aigSize} nodes."

  if cfg.graphviz then
    IO.FS.writeFile ("." / "aig.gv") <| AIG.toGraphviz entry

  let (cnf, map) ←
    withTraceNode `sat (fun _ => return "Converting AIG to CNF") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ =>
        let (entry, map) := entry.relabelNat'
        let cnf := AIG.toCNF entry
        (cnf, map)
      )

  let encoded ←
    withTraceNode `sat (fun _ => return "Converting frontend CNF to solver specific CNF") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ => LratFormula.ofCnf cnf)
  trace[sat] s!"CNF has {encoded.formula.clauses.size} clauses"

  let res ←
    withTraceNode `sat (fun _ => return "Obtaining external proof certificate") do
      runExternal encoded cfg.solver cfg.lratPath cfg.prevalidate cfg.timeout

  match res with
  | .ok cert =>
    let proof ← cert.toReflectionProof cfg bv ``verifyBVExpr ``unsat_of_verifyBVExpr_eq_true
    return ⟨proof, cert⟩
  | .error assignment =>
    let reconstructed := reconstructCounterExample map assignment aigSize atomsAssignment
    let mut error := m!"The prover found a potential counter example, consider the following assignment:\n"
    for (var, value) in reconstructed do
      error := error ++ m!"{var} = {value.bv}\n"
    throwError error

def reflectBV (g : MVarId) : M (BVLogicalExpr × (Expr → M Expr)) := g.withContext do
  let hyps ← getLocalHyps
  let sats ← hyps.filterMapM SatAtBVLogical.of
  if sats.size = 0 then
    let mut error := "None of the hypotheses are in the supported BitVec fragment.\n"
    error := error ++ "There are two potential fixes for this:\n"
    error := error ++ "1. If you are using custom BitVec constructs simplify them to built-in ones.\n"
    error := error ++ "2. If your problem is using only built-in ones it might currently be out of reach.\n"
    error := error ++ "   Consider expressing it in terms of different operations that are better supported."
    throwError error
  let sat := sats.foldl (init := SatAtBVLogical.trivial) SatAtBVLogical.and
  return (sat.bvExpr, sat.proveFalse)

def _root_.Lean.MVarId.closeWithBVReflection (g : MVarId)
    (unsatProver : UnsatProver) : MetaM LratCert := M.run do
  g.withContext do
    let (bvLogicalExpr, f) ←
      withTraceNode `bv (fun _ => return "Reflecting goal into BVLogicalExpr") do
        reflectBV g
    trace[bv] "Reflected bv logical expression: {bvLogicalExpr}"

    let atomsPairs := (← getThe State).atoms.toList.map (fun (expr, _, ident) => (ident, expr))
    let atomsAssignment := Batteries.HashMap.ofList atomsPairs
    let ⟨bvExprUnsat, cert⟩ ← unsatProver bvLogicalExpr atomsAssignment
    let proveFalse ← f bvExprUnsat
    g.assign proveFalse
    return cert

def _root_.Lean.MVarId.bvUnsat (g : MVarId) (cfg : TacticContext) : MetaM LratCert := M.run do
  let unsatProver : UnsatProver := fun bvExpr atomsAssignment => do
    withTraceNode `bv (fun _ => return "Preparing LRAT reflection term") do
      lratBitblaster cfg bvExpr atomsAssignment
  g.closeWithBVReflection unsatProver

structure Result where
  simpTrace : Simp.Stats
  lratCert : Option LratCert

def _root_.Lean.MVarId.bvDecide (g : MVarId) (cfg : TacticContext) : MetaM Result := do
  let ⟨g?, simpTrace⟩ ← g.bvNormalize
  let some g := g? | return ⟨simpTrace, none⟩
  let lratCert ← g.bvUnsat cfg
  return ⟨simpTrace, some lratCert⟩

/-
Close a goal by:
1. Turning it into a BitVec problem.
2. Using bitblasting to turn that into a SAT problem.
3. Running an external SAT solver on it and obtaining an LRAT proof from it.
4. Verifying the LRAT proof using proof by reflection.
-/
syntax (name := bvDecideSyntax) "bv_decide" : tactic

end BVDecide

open Elab.Tactic
elab_rules : tactic
  | `(tactic| bv_decide) => do
    let cfg ← BVDecide.TacticContext.new (← BVDecide.mkTemp)
    liftMetaFinishingTactic fun g => do
      let _ ← g.bvDecide cfg
      return ()
    -- the auto generated lratPath is a temp file that should be removed
    IO.FS.removeFile cfg.lratPath

