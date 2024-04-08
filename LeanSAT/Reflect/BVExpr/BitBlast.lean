import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.AIG

structure BVBit where
  {w : Nat}
  var : Nat
  idx : Fin w
  deriving Hashable, DecidableEq, Repr

instance : ToString BVBit where
  toString b := s!"x{b.var}[{b.idx.val}]"

instance : Inhabited BVBit where
  default :=
    {
        w := 1
        var := 0
        idx := 0
    }

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
        let ⟨⟨aig, lhsEntry, linv⟩, hlhs⟩ := go aig lhs idx hidx
        let ⟨⟨aig, rhsEntry, rinv⟩, hrhs⟩ := go aig rhs idx hidx
        let lhsRef := AIG.Ref.mk lhsEntry linv |>.cast <| by
          dsimp at hrhs ⊢
          omega
        let rhsRef := AIG.Ref.mk rhsEntry rinv
        ⟨
          aig.mkAndCached ⟨lhsRef, rhsRef⟩,
          by
            apply AIG.LawfulOperator.le_size_of_le_aig_size
            dsimp at hrhs hlhs ⊢
            omega
        ⟩
    | .un op expr =>
      match op with
      | .not =>
        let ⟨⟨aig, gateEntry, ginv⟩, hgate⟩ := go aig expr idx hidx
        ⟨
          aig.mkNotCached <| AIG.Ref.mk gateEntry ginv,
          by
            apply AIG.LawfulOperator.le_size_of_le_aig_size
            dsimp at hgate
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
  let ⟨laig, lhsEntry, linv⟩ := bitblast aig pair.leftBit
  match hr:bitblast laig pair.rightBit with
  | ⟨raig, rhsEntry, rinv⟩ =>
    let lhsRef := AIG.Ref.mk lhsEntry linv |>.cast <| by
      intro h
      dsimp at h ⊢
      have : raig = (bitblast laig pair.rightBit).aig := by simp [hr]
      rw [this]
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := bitblast)
      assumption
    let rhsRef := AIG.Ref.mk rhsEntry rinv
    raig.mkBEqCached ⟨lhsRef, rhsRef⟩

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

def mkEq (aig : AIG BVBit) (pair : ExprPair) : AIG.Entrypoint BVBit :=
  go aig pair.lhs pair.rhs pair.lhs.width (by simp [BVExpr.width])
where
  go {w : Nat} (aig : AIG BVBit) (lhs rhs : BVExpr w) (idx : Nat) (_hidx : idx ≤ w)
      : AIG.ExtendingEntrypoint aig :=
    match h:idx with
    | 0 => ⟨aig.mkConstCached true, by apply AIG.LawfulOperator.le_size⟩
    | nextBit + 1 =>
        let ⟨⟨aig, others, hothers⟩, hlt⟩ := go aig lhs rhs nextBit (by omega)
        match h2:BVExpr.mkBitEq aig ⟨lhs, rhs, nextBit, by omega⟩ with
        | ⟨naig, gate, hgate⟩ =>
          have : naig = (BVExpr.mkBitEq aig ⟨lhs, rhs, nextBit, by omega⟩).aig := by simp [h2]
          let othersRef := AIG.Ref.mk others hothers |>.cast <| by
            intro h
            rw [this]
            apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := BVExpr.mkBitEq)
            assumption
          let gateRef := AIG.Ref.mk gate hgate
          ⟨
            naig.mkAndCached ⟨gateRef, othersRef⟩,
            by
              apply AIG.LawfulOperator.le_size_of_le_aig_size
              rw [this]
              apply AIG.LawfulOperator.le_size_of_le_aig_size (f := BVExpr.mkBitEq)
              assumption
          ⟩

theorem mkEq.go_le_size (aig : AIG BVBit) (target : ExprPair) (start : Nat) {h}
    : aig.decls.size ≤ (mkEq.go aig target.lhs target.rhs start h).val.aig.decls.size := by
  exact (mkEq.go aig target.lhs target.rhs start h).property

theorem mkEq_le_size (aig : AIG BVBit) (target : ExprPair)
    : aig.decls.size ≤ (mkEq aig target).aig.decls.size := by
  unfold mkEq
  apply mkEq.go_le_size


theorem mkEq.go_decl_eq (aig : AIG BVBit) (target : ExprPair) (start : Nat) {h : idx < aig.decls.size}
    {h2} :
    have := mkEq.go_le_size aig target start
    (mkEq.go aig target.lhs target.rhs start h2).val.aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  induction start with
  | zero =>
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
  | succ curr ih =>
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkAndCached)]
    rw [AIG.LawfulOperator.decl_eq (f := BVExpr.mkBitEq)]
    . exact ih
    . apply Nat.lt_of_lt_of_le
      . exact h
      . apply AIG.LawfulOperator.le_size_of_le_aig_size (f := BVExpr.mkBitEq)
        apply mkEq.go_le_size


theorem mkEq_decl_eq (aig : AIG BVBit) (target : ExprPair) {h : idx < aig.decls.size} :
    have := mkEq_le_size aig target
    (mkEq aig target).aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  unfold mkEq
  exact mkEq.go_decl_eq aig target _

instance : AIG.LawfulOperator BVBit (fun _ => ExprPair) mkEq where
  le_size := mkEq_le_size
  decl_eq := by intros; apply mkEq_decl_eq

def mkNeq (aig : AIG BVBit) (pair : ExprPair) : AIG.Entrypoint BVBit :=
  let ⟨aig, gate, hgate⟩ := mkEq aig pair
  aig.mkNotCached (AIG.Ref.mk gate hgate)

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
