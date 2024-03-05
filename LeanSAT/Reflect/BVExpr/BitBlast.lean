import Std.Data.Fin.Basic
import Std.Data.BitVec.Lemmas
import LeanSAT.Reflect.BVExpr.Basic

open Std

structure BVBit where
  {w : Nat}
  var : Nat
  idx : Fin w

instance : ToString BVBit where
  toString b := s!"x{b.var}[{b.idx.val}]"

abbrev BVBitwise := BoolExpr BVBit

namespace BVBitwise

def eval (assign : BVExpr.Assignment) (expr : BVBitwise) : Bool :=
  BoolExpr.eval (fun bit => assign bit.var |>.snd.getLsb bit.idx.val) expr

@[simp] theorem eval_literal : eval assign (.literal bit) = (assign bit.var |>.snd.getLsb bit.idx.val) := rfl
@[simp] theorem eval_const : eval assign (.const b) = b := rfl
@[simp] theorem eval_not : eval assign (.not x) = !eval assign x := rfl
@[simp] theorem eval_gate : eval assign (.gate g x y) = g.eval (eval assign x) (eval assign y) := rfl

def sat (x : BVBitwise) (assign : BVExpr.Assignment) : Prop := eval assign x = true
def unsat (x : BVBitwise) : Prop := ∀ f, eval f x = false

end BVBitwise

namespace BVExpr

def bitblast (expr : BVExpr w) (idx : Fin w) : BVBitwise :=
  match expr with
  | .var varIdx => .literal ⟨varIdx, idx⟩
  | .const val => .const (val.getLsb idx.val)
  | .bin lhs op rhs =>
    match op with
    | .and =>
      let lhs := bitblast lhs idx
      let rhs := bitblast rhs idx
      .gate .and lhs rhs
  | .un op operand =>
    match op with
    | .not =>
      let operand := bitblast operand idx
      .not operand

theorem getLsb_eq_bitblast (expr : BVExpr w) (idx : Fin w) :
    ∀ assign, (expr.eval assign).getLsb idx.val = (expr.bitblast idx).eval assign := by
  intro assign
  induction expr with
  | var varIdx => simp [bitblast]
  | const bv => simp [bitblast]
  | bin lhs op rhs lih rih =>
    cases op with
    | and => simp[bitblast, Gate.eval, lih, rih]
  | un op operand ih =>
    cases op with
    | not => simp[ih, bitblast]

end BVExpr

namespace BVPred

def bitblast (expr : BVPred) : BVBitwise :=
  match expr with
  | @bin w lhs op rhs =>
    match op with
    | .eq => goEq lhs rhs w (by omega)
where
  mkEqBit {w : Nat} (lhs rhs : BVExpr w) (bit : Nat) (h : bit < w) : BVBitwise :=
    let blhs := lhs.bitblast ⟨bit, h⟩
    let brhs := rhs.bitblast ⟨bit, h⟩
    .gate .beq blhs brhs

  goEq {w : Nat} (lhs rhs : BVExpr w) (bit : Nat) (h : bit ≤ w) :=
    match h:bit with
    | 0 => .const true
    | rem + 1 => 
      let eq := mkEqBit lhs rhs rem (by omega)
      .gate .and eq (goEq lhs rhs rem (by omega))

theorem bitblast.mkEqBit_correct (idx : Fin w) : 
    (bitblast.mkEqBit lhs rhs idx.val idx.isLt).eval assign 
      =
    ((lhs.eval assign).getLsb idx.val = (rhs.eval assign).getLsb idx.val) := by
  simp[mkEqBit, Gate.eval, BVExpr.getLsb_eq_bitblast]


theorem bitblast.mkEqBit_correct' : 
    (∀ (idx : Fin w), (bitblast.mkEqBit lhs rhs idx.val idx.isLt).eval assign)
      = 
    (lhs.eval assign = rhs.eval assign) := by
  simp only [eq_iff_iff]
  constructor
  . intro h; 
    apply BitVec.eq_of_getLsb_eq
    intro idx
    rw [← bitblast.mkEqBit_correct]
    apply h
  . intro h idx
    simp [bitblast.mkEqBit_correct, h]

theorem Fin.forall_succ (p : Fin (n + 1) → Prop) [DecidablePred p] :
    (∀ (x : Fin (n + 1)), p x) ↔ (p (Fin.last _) ∧ ∀ (x : Fin n), p (x.castAdd 1)) :=
  ⟨fun w => ⟨w _, fun i => w _⟩, fun ⟨h, w⟩ x =>
    if p : x = Fin.last _ then by
      subst p; exact h
    else by
      -- This line is needed now that `omega` doesn't check defeq on atoms.
      simp [Fin.last, ← Fin.val_ne_iff] at p
      have t : x < n := by omega
      rw [show x = Fin.castAdd 1 ⟨x, by omega⟩ by rfl]
      apply w⟩

theorem bitblast.aux :
   (∀ (idx : Fin w), (bitblast.mkEqBit lhs rhs idx.val idx.isLt).eval assign)
     = 
   (goEq lhs rhs w (by omega)).eval assign := by
  induction w with
  | zero => 
    simp[goEq]
    intro idx
    cases idx.isLt
  | succ w ih => 
    simp only [goEq, BVBitwise.eval_gate, Gate.eval, Bool.and_eq_true, eq_iff_iff]
    constructor
    . intro h
      constructor
      . apply h ⟨w, (by omega)⟩
      . rw [Fin.forall_succ] at h
        rcases h with ⟨h1, h2⟩
        -- TODO: this is almost IH now
        sorry
    . intro h
      rw [Fin.forall_succ]
      rcases h with ⟨h1, h2⟩
      constructor
      . simp[h1]
      . intro x
        simp only [Fin.coe_castAdd]
        -- TODO: this is almost IH now
        sorry

theorem bitblast.goEq_correct' {lhs rhs : BVExpr w} :
    ((goEq lhs rhs w (by omega)).eval assign)
      ↔
    ((BVPred.bin lhs .eq rhs).eval assign) := by
  rw [← bitblast.aux]
  rw [bitblast.mkEqBit_correct']
  simp

-- TODO: unclear how to get from ' to here
theorem bitblast.goEq_correct {lhs rhs : BVExpr w} :
    ((goEq lhs rhs w (by omega)).eval assign)
      =
    ((BVPred.bin lhs .eq rhs).eval assign) := by
  sorry

theorem eq_bitblast (expr : BVPred) : ∀ assign, expr.eval assign = expr.bitblast.eval assign := by
  intro assign
  cases expr with
  | @bin w lhs op rhs =>
    cases op with
    | eq => simp [bitblast, bitblast.goEq_correct]

end BVPred

namespace BVLogicalExpr

def bitblast (expr : BVLogicalExpr) : BVBitwise :=
  match expr with
  | .literal pred => pred.bitblast
  | .gate g x y => .gate g (bitblast x) (bitblast y)
  | .not x => .not (bitblast x)
  | .const b => .const b

theorem eq_bitblast (expr : BVLogicalExpr) : ∀ assign, expr.eval assign = expr.bitblast.eval assign := by
  intro assign
  induction expr with
  | literal pred => simp[bitblast, BVPred.eq_bitblast]
  | gate g lhs rhs lih rih => simp[bitblast, lih, rih]
  | not op ih => simp[bitblast, ih]
  | const b => simp[bitblast]

theorem unsat_iff_bitblast_unsat (expr : BVLogicalExpr) : expr.unsat ↔ expr.bitblast.unsat := by
  constructor
  . intro h assign
    rw[← eq_bitblast]
    apply h
  . intro h assign
    rw [eq_bitblast]
    apply h

end BVLogicalExpr

open BitVec
#eval
  let pred : BVLogicalExpr := .literal (.bin (.bin (w := 2) (.var 1) .and (.var 0)) .eq (.bin (.var 0) .and (.var 1)))
  toString pred.bitblast
