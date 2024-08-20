/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Frontend.BVDecide.Reflect

/-!
Provides the logic for reifying `BitVec` expressions.
-/

namespace LeanSAT
namespace BVDecide

open Lean
open Lean.Meta
open Lean.Elab.Tactic.BVDecide

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

theorem shiftLeftNat_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h : x = x') :
    x' <<< n = x <<< n := by
  simp[*]

theorem shiftLeft_congr (m n : Nat) (lhs : BitVec m) (rhs : BitVec n) (lhs' : BitVec m)
    (rhs' : BitVec n) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs <<< rhs = lhs' <<< rhs' := by
  simp[*]

theorem shiftRightNat_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h : x = x') :
    x' >>> n = x >>> n := by
  simp[*]

theorem shiftRight_congr (m n : Nat) (lhs : BitVec m) (rhs : BitVec n) (lhs' : BitVec m)
    (rhs' : BitVec n) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs >>> rhs = lhs' >>> rhs' := by
  simp[*]

theorem arithShiftRight_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h : x = x') :
    BitVec.sshiftRight x' n = BitVec.sshiftRight x n := by
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

theorem append_congr (lw rw : Nat) (lhs lhs' : BitVec lw) (rhs rhs' : BitVec rw) (h1 : lhs' = lhs)
    (h2 : rhs' = rhs) :
    lhs' ++ rhs' = lhs ++ rhs := by
  simp[*]

theorem replicate_congr (n : Nat) (w : Nat) (expr expr' : BitVec w) (h : expr' = expr) :
    BitVec.replicate n expr' = BitVec.replicate n expr := by
  simp[*]

theorem extract_congr (hi lo : Nat) (w : Nat) (x x' : BitVec w) (h1 : x = x') :
    BitVec.extractLsb hi lo x' = BitVec.extractLsb hi lo x := by
  simp[*]

theorem rotateLeft_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h : x = x') :
    BitVec.rotateLeft x' n = BitVec.rotateLeft x n := by
  simp[*]

theorem rotateRight_congr (n : Nat) (w : Nat) (x x' : BitVec w) (h : x = x') :
    BitVec.rotateRight x' n = BitVec.rotateRight x n := by
  simp[*]

theorem mul_congr (w : Nat) (lhs rhs lhs' rhs' : BitVec w) (h1 : lhs' = lhs) (h2 : rhs' = rhs) :
    lhs' * rhs' = lhs * rhs := by
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
  | HAnd.hAnd _ _ _ _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .and ``and_congr
  | HOr.hOr _ _ _ _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .or ``or_congr
  | HXor.hXor _ _ _ _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .xor ``xor_congr
  | HAdd.hAdd _ _ _ _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .add ``add_congr
  | HMul.hMul _ _ _ _ lhsExpr rhsExpr =>
    binaryReflection lhsExpr rhsExpr .mul ``mul_congr
  | Complement.complement _ _ innerExpr =>
    unaryReflection innerExpr .not ``not_congr
  | HShiftLeft.hShiftLeft _ β _ _ innerExpr distanceExpr =>
    let distance? ← getNatOrBvValue? β distanceExpr
    if distance?.isSome then
      shiftConstReflection
        β
        distanceExpr
        innerExpr
        .shiftLeftConst
        ``BVUnOp.shiftLeftConst
        ``shiftLeftNat_congr
    else
      shiftReflection
        β
        distanceExpr
        innerExpr
        .shiftLeft
        ``BVExpr.shiftLeft
        ``shiftLeft_congr
  | HShiftRight.hShiftRight _ β _ _ innerExpr distanceExpr =>
    let distance? ← getNatOrBvValue? β distanceExpr
    if distance?.isSome then
      shiftConstReflection
        β
        distanceExpr
        innerExpr
        .shiftRightConst
        ``BVUnOp.shiftRightConst
        ``shiftRightNat_congr
    else
      shiftReflection
        β
        distanceExpr
        innerExpr
        .shiftRight
        ``BVExpr.shiftRight
        ``shiftRight_congr
  | BitVec.sshiftRight _ innerExpr distanceExpr =>
    let some distance ← getNatValue? distanceExpr | return ← ofAtom x
    shiftConstLikeReflection
      distance
      innerExpr
      .arithShiftRightConst
      ``BVUnOp.arithShiftRightConst
      ``arithShiftRight_congr
  | BitVec.zeroExtend _ newWidthExpr innerExpr =>
    let some newWidth ← getNatValue? newWidthExpr | return ← ofAtom x
    let some inner ← ofOrAtom innerExpr | return none
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
      return mkApp5 (mkConst ``zeroExtend_congr)
        newWidthExpr
        (toExpr inner.width)
        innerExpr
        innerEval
        innerProof
    return some ⟨newWidth, bvExpr, proof, expr⟩
  | BitVec.signExtend _ newWidthExpr innerExpr =>
    let some newWidth ← getNatValue? newWidthExpr | return ← ofAtom x
    let some inner ← ofOrAtom innerExpr | return none
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
      return mkApp5 (mkConst ``signExtend_congr)
        newWidthExpr
        (toExpr inner.width)
        innerExpr
        innerEval
        innerProof
    return some ⟨newWidth, bvExpr, proof, expr⟩
  | HAppend.hAppend _ _ _ _ lhsExpr rhsExpr =>
    let some lhs ← ofOrAtom lhsExpr | return none
    let some rhs ← ofOrAtom rhsExpr | return none
    let bvExpr := .append lhs.bvExpr rhs.bvExpr
    let expr := mkApp4 (mkConst ``BVExpr.append)
      (toExpr lhs.width)
      (toExpr rhs.width)
      lhs.expr rhs.expr
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
  | BitVec.replicate _ nExpr innerExpr =>
    let some inner ← ofOrAtom innerExpr | return none
    let some n ← getNatValue? nExpr | return ← ofAtom x
    let bvExpr := .replicate n inner.bvExpr
    let expr := mkApp3 (mkConst ``BVExpr.replicate)
      (toExpr inner.width)
      (toExpr n)
      inner.expr
    let proof := do
      let innerEval ← mkEvalExpr inner.width inner.expr
      let innerProof ← inner.evalsAtAtoms
      return mkApp5 (mkConst ``replicate_congr)
        (toExpr n)
        (toExpr inner.width)
        innerExpr
        innerEval
        innerProof
    return some ⟨inner.width * n, bvExpr, proof, expr⟩
  | BitVec.extractLsb _ hiExpr loExpr innerExpr =>
    let some hi ← getNatValue? hiExpr | return ← ofAtom x
    let some lo ← getNatValue? loExpr | return ← ofAtom x
    let some inner ← ofOrAtom innerExpr | return none
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

  ofOrAtom (x : Expr) : M (Option ReifiedBVExpr) := do
    let res ← of x
    match res with
    | some exp => return some exp
    | none => ofAtom x

  shiftConstLikeReflection (distance : Nat) (innerExpr : Expr) (shiftOp : Nat → BVUnOp)
      (shiftOpName : Name) (congrThm : Name) :
      M (Option ReifiedBVExpr) := do
    let some inner ← ofOrAtom innerExpr | return none
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

  rotateReflection (distanceExpr : Expr) (innerExpr : Expr) (rotateOp : Nat → BVUnOp)
      (rotateOpName : Name) (congrThm : Name) :
      M (Option ReifiedBVExpr) := do
    -- Either the shift values are constant or we abstract the entire term as atoms
    let some distance ← getNatValue? distanceExpr | return ← ofAtom x
    shiftConstLikeReflection distance innerExpr rotateOp rotateOpName congrThm

  shiftConstReflection (β : Expr) (distanceExpr : Expr) (innerExpr : Expr) (shiftOp : Nat → BVUnOp)
      (shiftOpName : Name) (congrThm : Name) :
      M (Option ReifiedBVExpr) := do
    -- Either the shift values are constant or we abstract the entire term as atoms
    let some distance ← getNatOrBvValue? β distanceExpr | return ← ofAtom x
    shiftConstLikeReflection distance innerExpr shiftOp shiftOpName congrThm

  shiftReflection (β : Expr) (distanceExpr : Expr) (innerExpr : Expr)
      (shiftOp : {m n : Nat} → BVExpr m → BVExpr n → BVExpr m) (shiftOpName : Name)
      (congrThm : Name) :
      M (Option ReifiedBVExpr) := do
    let_expr BitVec _ ← β | return ← ofAtom x
    let some inner ← of innerExpr | return none
    let some distance ← of distanceExpr | return none
    let bvExpr : BVExpr inner.width := shiftOp inner.bvExpr distance.bvExpr
    let expr :=
      mkApp4
        (mkConst shiftOpName)
        (toExpr inner.width)
        (toExpr distance.width)
        inner.expr
        distance.expr
    let congrProof :=
      mkApp2
        (mkConst congrThm)
        (toExpr inner.width)
        (toExpr distance.width)
    let proof := binaryCongrProof inner distance innerExpr distanceExpr congrProof
    return some ⟨inner.width, bvExpr, proof, expr⟩

  binaryReflection (lhsExpr rhsExpr : Expr) (op : BVBinOp) (congrThm : Name) :
      M (Option ReifiedBVExpr) := do
    let some lhs ← ofOrAtom lhsExpr | return none
    let some rhs ← ofOrAtom rhsExpr | return none
    if h : rhs.width = lhs.width then
      let bvExpr : BVExpr lhs.width := .bin lhs.bvExpr op (h ▸ rhs.bvExpr)
      let expr := mkApp4 (mkConst ``BVExpr.bin) (toExpr lhs.width) lhs.expr (toExpr op) rhs.expr
      let congrThm := mkApp (mkConst congrThm) (toExpr lhs.width)
      let proof := binaryCongrProof lhs rhs lhsExpr rhsExpr congrThm
      return some ⟨lhs.width, bvExpr, proof, expr⟩
    else
      return none

  binaryCongrProof (lhs rhs : ReifiedBVExpr) (lhsExpr rhsExpr : Expr) (congrThm : Expr) :
      M Expr := do
    let lhsEval ← mkEvalExpr lhs.width lhs.expr
    let lhsProof ← lhs.evalsAtAtoms
    let rhsProof ← rhs.evalsAtAtoms
    let rhsEval ← mkEvalExpr rhs.width rhs.expr
    return mkApp6 congrThm lhsExpr rhsExpr lhsEval rhsEval lhsProof rhsProof

  unaryReflection (innerExpr : Expr) (op : BVUnOp) (congrThm : Name) :
      M (Option ReifiedBVExpr) := do
    let some inner ← ofOrAtom innerExpr | return none
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

end BVDecide
end LeanSAT
