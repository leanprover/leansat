import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.AIG

structure BVBit where
  {w : Nat}
  var : Nat
  idx : Fin w
  deriving Hashable, DecidableEq, Repr

instance : ToString BVBit where
  toString b := s!"x{b.var}[{b.idx.val}]"

namespace BVExpr

structure SingleBit where
  {w : Nat}
  expr : BVExpr w
  idx : Nat
  hidx : idx < w

def bitblast (aig : AIG BVBit) (target : SingleBit) : AIG.Entrypoint BVBit :=
  go aig target.expr target.idx target.hidx |>.val
where
  go {w : Nat} (aig : AIG BVBit) (expr : BVExpr w) (idx : Nat) (hidx : idx < w)
      : AIG.ExtendingEntrypoint aig :=
    match expr with
    | .var a => ⟨aig.mkAtomCached ⟨a, ⟨idx, hidx⟩⟩, by apply AIG.LawfulOperator.le_size⟩
    | .const val => ⟨aig.mkConstCached (val.getLsb idx), by apply AIG.LawfulOperator.le_size⟩
    | .bin lhs op rhs =>
      match op with
      | .and =>
        let ⟨lhsEntry, hlhs⟩ := go aig lhs idx hidx
        let ⟨rhsEntry, hrhs⟩ := go lhsEntry.aig rhs idx hidx
        let lhsRef := AIG.Ref.ofEntrypoint lhsEntry |>.cast (by omega)
        let rhsRef := AIG.Ref.ofEntrypoint rhsEntry
        ⟨
          rhsEntry.aig.mkAndCached ⟨lhsRef, rhsRef⟩,
          by
            apply AIG.LawfulOperator.le_size_of_le_aig_size
            omega
        ⟩
    | .un op expr =>
      match op with
      | .not =>
        let ⟨gateEntry, hgate⟩ := go aig expr idx hidx
        ⟨
          gateEntry.aig.mkNotCached <| AIG.Ref.ofEntrypoint gateEntry,
          by
            apply AIG.LawfulOperator.le_size_of_le_aig_size
            omega
        ⟩

theorem bitblast_le_size (aig : AIG BVBit) (target : SingleBit)
    : aig.decls.size ≤ (bitblast aig target).aig.decls.size := by
  have := bitblast.go aig target.expr target.idx target.hidx |>.property
  unfold bitblast
  omega

theorem bitblast.go_decl_eq (aig : AIG BVBit) (expr : BVExpr w) (bitidx : Nat) (hidx : bitidx < w)
    {h : idx < aig.decls.size} :
    have := (bitblast.go aig expr bitidx hidx).property
    (go aig expr bitidx hidx).val.aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  induction expr generalizing aig with
  | var =>
    dsimp [go]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkAtomCached)]
  | const =>
    dsimp [go]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
  | bin lhs op rhs lih rih =>
    cases op with
    | and =>
      dsimp [go]
      rw [AIG.LawfulOperator.decl_eq (f := AIG.mkAndCached)]
      rw [rih, lih]
  | un op expr ih =>
    cases op with
    | not =>
      dsimp [go]
      rw [AIG.LawfulOperator.decl_eq (f := AIG.mkNotCached)]
      rw [ih]

theorem bitblast_decl_eq (aig : AIG BVBit) (target : SingleBit) {h : idx < aig.decls.size} :
    have := bitblast_le_size aig target
    (bitblast aig target).aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  unfold bitblast
  dsimp
  rw [bitblast.go_decl_eq]

instance : AIG.LawfulOperator BVBit (fun _ => SingleBit) bitblast where
  le_size := bitblast_le_size
  decl_eq := by intros; apply bitblast_decl_eq

structure BitPair where
  {w : Nat}
  lhs : BVExpr w
  rhs : BVExpr w
  idx : Nat
  hidx : idx < w

def BitPair.leftBit (pair : BitPair) : SingleBit :=
  {
    expr := pair.lhs
    idx := pair.idx
    hidx := pair.hidx
  }

def BitPair.rightBit (pair : BitPair) : SingleBit :=
  {
    expr := pair.rhs
    idx := pair.idx
    hidx := pair.hidx
  }

def mkBitEq (aig : AIG BVBit) (pair : BitPair) : AIG.Entrypoint BVBit :=
  let lhsEntry := bitblast aig pair.leftBit
  let rhsEntry := bitblast lhsEntry.aig pair.rightBit
  let lhsRef := AIG.Ref.ofEntrypoint lhsEntry |>.cast <| by
    intros
    apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := bitblast)
    assumption
  let rhsRef := AIG.Ref.ofEntrypoint rhsEntry
  rhsEntry.aig.mkBEqCached ⟨lhsRef, rhsRef⟩

theorem mkBitEq_le_size (aig : AIG BVBit) (target : BitPair)
    : aig.decls.size ≤ (mkBitEq aig target).aig.decls.size := by
  unfold mkBitEq
  dsimp
  apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkBEqCached)
  apply AIG.LawfulOperator.le_size_of_le_aig_size (f := bitblast)
  apply AIG.LawfulOperator.le_size

theorem mkBitEq_decl_eq (aig : AIG BVBit) (target : BitPair) {h : idx < aig.decls.size} :
    have := mkBitEq_le_size aig target
    (mkBitEq aig target).aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  unfold mkBitEq
  dsimp
  rw [AIG.LawfulOperator.decl_eq (f := AIG.mkBEqCached)]
  rw [AIG.LawfulOperator.decl_eq (f := bitblast)]
  . rw [AIG.LawfulOperator.decl_eq (f := bitblast)]
    apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := bitblast)
    assumption
  . apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := bitblast)
    apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := bitblast)
    assumption

instance : AIG.LawfulOperator BVBit (fun _ => BitPair) mkBitEq where
  le_size := mkBitEq_le_size
  decl_eq := by intros; apply mkBitEq_decl_eq

end BVExpr

namespace BVPred

structure ExprPair where
  {w : Nat}
  lhs : BVExpr w
  rhs : BVExpr w

-- FIXME: workaround Meta.check perf issue
def mkEq.go {w : Nat} (aig : AIG BVBit) (lhs rhs : BVExpr w) (idx : Nat) (_hidx : idx ≤ w)
    : AIG.ExtendingEntrypoint aig :=
  match h:idx with
  | 0 => ⟨aig.mkConstCached true, by apply AIG.LawfulOperator.le_size⟩
  | nextBit + 1 =>
    let ⟨others, _⟩ := go aig lhs rhs nextBit (by omega)
    let gate := BVExpr.mkBitEq others.aig ⟨lhs, rhs, nextBit, by omega⟩
    let othersRef := AIG.Ref.ofEntrypoint others |>.cast <| by
      intros
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := BVExpr.mkBitEq)
      assumption
    let gateRef := AIG.Ref.ofEntrypoint gate
    ⟨
      gate.aig.mkAndCached ⟨gateRef, othersRef⟩,
      by
        apply AIG.LawfulOperator.le_size_of_le_aig_size
        apply AIG.LawfulOperator.le_size_of_le_aig_size (f := BVExpr.mkBitEq)
        assumption
    ⟩

def mkEq (aig : AIG BVBit) (pair : ExprPair) : AIG.Entrypoint BVBit :=
  mkEq.go aig pair.lhs pair.rhs pair.lhs.width (by simp [BVExpr.width])


theorem mkEq.go_le_size (aig : AIG BVBit) (target : ExprPair) (start : Nat)
    : aig.decls.size ≤ (mkEq.go aig target.lhs target.rhs start sorry).val.aig.decls.size := by
  exact (mkEq.go aig target.lhs target.rhs start sorry).property

theorem mkEq_le_size (aig : AIG BVBit) (target : ExprPair)
    : aig.decls.size ≤ (mkEq aig target).aig.decls.size := by
  unfold mkEq
  exact (mkEq.go aig target.lhs target.rhs (BVExpr.width target.lhs) (by simp [BVExpr.width])).property


theorem mkEq.go_decl_eq (aig : AIG BVBit) (target : ExprPair) (start : Nat) {h : idx < aig.decls.size} :
    have := mkEq.go_le_size aig target start
    (mkEq.go aig target.lhs target.rhs start sorry).val.aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  -- simp [go] again gets crushed by Meta.check here.
  induction start with
  | zero => sorry
  | succ curr ih => sorry

theorem mkEq_decl_eq (aig : AIG BVBit) (target : ExprPair) {h : idx < aig.decls.size} :
    have := mkEq_le_size aig target
    (mkEq aig target).aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  unfold mkEq
  exact mkEq.go_decl_eq aig target _

instance : AIG.LawfulOperator BVBit (fun _ => ExprPair) mkEq where
  le_size := mkEq_le_size
  decl_eq := by intros; apply mkEq_decl_eq

def mkNeq (aig : AIG BVBit) (pair : ExprPair) : AIG.Entrypoint BVBit :=
  let gate := mkEq aig pair
  gate.aig.mkNotCached (AIG.Ref.ofEntrypoint gate)

theorem mkNeq_le_size (aig : AIG BVBit) (target : ExprPair)
    : aig.decls.size ≤ (mkNeq aig target).aig.decls.size := by
  unfold mkNeq
  dsimp
  apply AIG.LawfulOperator.le_size_of_le_aig_size
  apply AIG.LawfulOperator.le_size

theorem mkNeq_decl_eq (aig : AIG BVBit) (target : ExprPair) {h : idx < aig.decls.size} :
    have := mkNeq_le_size aig target
    (mkNeq aig target).aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  unfold mkNeq
  dsimp
  rw [AIG.LawfulOperator.decl_eq]
  rw [AIG.LawfulOperator.decl_eq (f := mkEq)]
  apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := mkEq)
  assumption

instance : AIG.LawfulOperator BVBit (fun _ => ExprPair) mkNeq where
  le_size := mkNeq_le_size
  decl_eq := by intros; apply mkNeq_decl_eq

def bitblast (aig : AIG BVBit) (pred : BVPred) : AIG.Entrypoint BVBit :=
  match pred with
  | .bin lhs op rhs =>
    match op with
    | .eq => mkEq aig ⟨lhs, rhs⟩
    | .neq => mkNeq aig ⟨lhs, rhs⟩

theorem bitblast_le_size (aig : AIG BVBit) (pred : BVPred)
    : aig.decls.size ≤ (bitblast aig pred).aig.decls.size := by
  cases pred with
  | bin lhs op rhs =>
    cases op with
    | eq =>
      simp only [bitblast]
      apply AIG.LawfulOperator.le_size
    | neq =>
      simp only [bitblast]
      apply AIG.LawfulOperator.le_size

theorem bitblast_decl_eq (aig : AIG BVBit) (pred : BVPred) {h : idx < aig.decls.size} :
    have := bitblast_le_size aig pred
    (bitblast aig pred).aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  cases pred with
  | bin lhs op rhs =>
    cases op with
    | eq =>
      simp only [bitblast]
      rw [AIG.LawfulOperator.decl_eq (f := mkEq)]
    | neq =>
      simp only [bitblast]
      rw [AIG.LawfulOperator.decl_eq (f := mkNeq)]

instance : AIG.LawfulOperator BVBit (fun _ => BVPred) bitblast where
  le_size := bitblast_le_size
  decl_eq := by intros; apply bitblast_decl_eq

end BVPred

namespace BVLogicalExpr

def bitblast (expr : BVLogicalExpr) : AIG.Entrypoint BVBit :=
  AIG.ofBoolExprCached expr BVPred.bitblast

end BVLogicalExpr

open BitVec
#eval
  let pred : BVLogicalExpr := .literal (.bin (.bin (w := 8) (.var 1) .and (.var 0)) .eq (.bin (.var 0) .and (.var 1)))
  pred.bitblast.aig.decls.size
