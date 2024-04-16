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

namespace bitblast


-- TODO: Probably a more general thing that we should put somewhere else
structure BVVar (width : Nat) where
  ident : Nat

def blastVar (aig : AIG BVBit) (var : BVVar w) : AIG.RefStreamEntry BVBit w :=
  go w aig 0 .empty var.ident (by omega)
where
  go (w : Nat) (aig : AIG BVBit) (idx : Nat) (s : AIG.RefStream aig idx) (a : Nat)
    (hidx : idx ≤ w)
    : AIG.RefStreamEntry BVBit w :=
  if hidx:idx < w then
    match haig:aig.mkAtomCached ⟨a, ⟨idx, hidx⟩⟩ with
    | ⟨newAig, bitRef⟩ =>
      let s := s.cast <| by
        intros
        have : newAig = (aig.mkAtomCached ⟨a, ⟨idx, hidx⟩⟩).aig := by rw [haig]
        rw[this]
        apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkAtomCached)
        assumption
      let s := s.pushRef bitRef
      go w newAig (idx + 1) s a (by omega)
  else
    have hidx : idx = w := by omega
    ⟨aig, hidx ▸ s⟩
  termination_by w - idx

theorem blastVar.go_le_size {aig : AIG BVBit} (idx : Nat) (s : AIG.RefStream aig idx) (a : Nat)
    (hidx : idx ≤ w)
    : aig.decls.size ≤ (go w aig idx s a hidx).aig.decls.size := by
  unfold go
  split
  . dsimp
    refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulOperator.le_size
  . simp
termination_by w - idx

theorem blastVar_le_size {aig : AIG BVBit} (var : BVVar w)
    : aig.decls.size ≤ (blastVar aig var).aig.decls.size := by
  unfold blastVar
  apply blastVar.go_le_size

theorem blastVar.go_decl_eq? {aig : AIG BVBit} (i : Nat) (s : AIG.RefStream aig i) (a : Nat)
    (hi : i ≤ w)
    : ∀ (idx : Nat) (_hidx : idx < aig.decls.size),
        (go w aig i s a hi).aig.decls[idx]? = aig.decls[idx]? := by
  intro idx hidx
  unfold go
  split
  . dsimp
    rw [go_decl_eq?]
    rw [Array.getElem?_lt, Array.getElem?_lt]
    . rw [AIG.LawfulOperator.decl_eq (f := AIG.mkAtomCached)]
      . apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkAtomCached)
        assumption
      . assumption
    . apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkAtomCached)
      assumption
  . simp
termination_by w - i

theorem blastVar.go_decl_eq {aig : AIG BVBit} (i : Nat) (s : AIG.RefStream aig i) (a : Nat)
    (hi : i ≤ w)
    : ∀ (idx : Nat) (h1) (h2), (go w aig i s a hi).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  have := go_decl_eq? i s a hi idx h1
  rw [Array.getElem?_lt, Array.getElem?_lt] at this
  injection this

theorem blastVar_decl_eq {aig : AIG BVBit} (var : BVVar w)
    : ∀ (idx : Nat) (h1) (h2), (blastVar aig var).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  unfold blastVar
  apply blastVar.go_decl_eq

instance : AIG.LawfulStreamOperator BVBit (fun _ w => BVVar w) blastVar where
  le_size := by intros; apply blastVar_le_size
  decl_eq := by intros; apply blastVar_decl_eq

def blastConst (aig : AIG BVBit) (val : BitVec w) : AIG.RefStreamEntry BVBit w :=
  go aig 0 .empty val (by omega)
where
  go {w : Nat} (aig : AIG BVBit) (idx : Nat) (s : AIG.RefStream aig idx) (val : BitVec w)
      (hidx : idx ≤ w)
      : AIG.RefStreamEntry BVBit w :=
    if hidx:idx < w then
      match haig:aig.mkConstCached (val.getLsb idx) with
      | ⟨newAig, bitRef⟩ =>
        let s := s.cast <| by
          intros
          have : newAig = (aig.mkConstCached (val.getLsb idx)).aig := by rw [haig]
          rw [this]
          apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
          assumption
        let s := s.pushRef bitRef
        go newAig (idx + 1) s val (by omega)
    else
      have hidx : idx = w := by omega
      ⟨aig, hidx ▸ s⟩
  termination_by w - idx

theorem blastConst.go_le_size {aig : AIG BVBit} (idx : Nat) (s : AIG.RefStream aig idx) (val : BitVec w)
    (hidx : idx ≤ w)
    : aig.decls.size ≤ (go aig idx s val hidx).aig.decls.size := by
  unfold go
  split
  . dsimp
    refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulOperator.le_size
  . simp
termination_by w - idx

theorem blastConst_le_size {aig : AIG BVBit} (val : BitVec w)
    : aig.decls.size ≤ (blastConst aig val).aig.decls.size := by
  unfold blastConst
  apply blastConst.go_le_size

theorem blastConst.go_decl_eq? {aig : AIG BVBit} (i : Nat) (s : AIG.RefStream aig i) (val : BitVec w)
    (hi : i ≤ w)
    : ∀ (idx : Nat) (_hidx : idx < aig.decls.size),
        (go aig i s val hi).aig.decls[idx]? = aig.decls[idx]? := by
  intro idx hidx
  unfold go
  split
  . dsimp
    rw [blastConst.go_decl_eq?]
    rw [Array.getElem?_lt, Array.getElem?_lt]
    . rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
      . apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
        assumption
      . assumption
    . apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      assumption
  . simp
termination_by w - i

theorem blastConst.go_decl_eq {aig : AIG BVBit} (i : Nat) (s : AIG.RefStream aig i) (val : BitVec w)
    (hi : i ≤ w)
    : ∀ (idx : Nat) (h1) (h2),
        (go aig i s val hi).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  have := blastConst.go_decl_eq? i s val hi idx h1
  rw [Array.getElem?_lt, Array.getElem?_lt] at this
  injection this

theorem blastConst_decl_eq {aig : AIG BVBit} (val : BitVec w)
    : ∀ (idx : Nat) (h1) (h2),
        (blastConst aig val).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros
  unfold blastConst
  apply blastConst.go_decl_eq

instance : AIG.LawfulStreamOperator BVBit (fun _ w => BitVec w) blastConst where
  le_size := by intros; apply blastConst_le_size
  decl_eq := by intros; apply blastConst_decl_eq

end bitblast

def bitblast (aig : AIG BVBit) (expr : BVExpr w) : AIG.RefStreamEntry BVBit w :=
  go aig expr |>.val
where
  go (aig : AIG BVBit) (expr : BVExpr w) : AIG.ExtendingRefStreamEntry aig w :=
    match expr with
    | .var a =>
      match haig:bitblast.blastVar aig ⟨a⟩ with
      | ⟨newAig, s⟩ =>
        -- TODO: Think of a way to prettify these theorems
        ⟨
          ⟨newAig, s⟩,
          by
            have : newAig = (bitblast.blastVar aig ⟨a⟩).aig := by
              rw [haig]
            simp only [this]
            apply AIG.LawfulStreamOperator.le_size
        ⟩
    | .const val =>
      match haig:bitblast.blastConst aig val with
      | ⟨newAig, s⟩ =>
        ⟨
          ⟨newAig, s⟩,
          by
            have : newAig = (bitblast.blastConst aig val).aig := by
              simp [haig]
            simp only [this]
            apply AIG.LawfulStreamOperator.le_size
        ⟩
    | .bin lhs op rhs =>
      match op with
      | .and =>
        match go aig lhs with
        | ⟨⟨laig, lhs⟩, hlaig⟩ =>
          match go laig rhs with
          | ⟨⟨raig, rhs⟩, hraig⟩ =>
            let lhs := lhs.cast <| by
              intro i hi
              dsimp at hlaig hraig
              omega
            match hfinal:AIG.RefStream.zip raig ⟨lhs, rhs, AIG.mkAndCached⟩ with
            | ⟨finalAig, s⟩ =>
              ⟨
                ⟨finalAig, s⟩,
                by
                  have : finalAig = (AIG.RefStream.zip raig ⟨lhs, rhs, AIG.mkAndCached⟩).aig := by
                    simp [hfinal]
                  simp only [this]
                  apply AIG.LawfulStreamOperator.le_size_of_le_aig_size
                  dsimp at hlaig hraig
                  omega
              ⟩
    | .un op expr =>
      match op with
      | .not =>
        match go aig expr with
        | ⟨⟨eaig, estream⟩, heaig⟩ =>
          match hfinal:AIG.RefStream.map eaig ⟨estream, AIG.mkNotCached⟩ with
          | ⟨finalAig, s⟩ =>
            ⟨
              ⟨finalAig, s⟩,
              by
                have : finalAig = (AIG.RefStream.map eaig ⟨estream, AIG.mkNotCached⟩).aig := by
                  simp [hfinal]
                simp only [this]
                apply AIG.LawfulStreamOperator.le_size_of_le_aig_size
                dsimp at heaig
                omega
            ⟩

theorem bitblast_le_size {aig : AIG BVBit} (expr : BVExpr w)
    : aig.decls.size ≤ (bitblast aig expr).aig.decls.size := by
  unfold bitblast
  exact (bitblast.go aig expr).property

theorem bitblast.go_decl_eq? (aig : AIG BVBit) (expr : BVExpr w)
    : ∀ (idx : Nat) (_hidx : idx < aig.decls.size),
        (go aig expr).val.aig.decls[idx]? = aig.decls[idx]? := by
  intro idx hidx
  induction expr generalizing aig with
  | var =>
    dsimp [go]
    rw [Array.getElem?_lt, Array.getElem?_lt]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastVar)]
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastVar)
      assumption
    . assumption
  | const =>
    dsimp [go]
    rw [Array.getElem?_lt, Array.getElem?_lt]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastConst)]
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastConst)
      assumption
    . assumption
  | bin lhs op rhs lih rih =>
    cases op with
    | and =>
      dsimp [go]
      rw [Array.getElem?_lt, Array.getElem?_lt]
      rw [AIG.LawfulStreamOperator.decl_eq]
      rw [← Array.getElem?_lt, ← Array.getElem?_lt]
      rw [rih, lih]
      -- TODO: for some reason my usual omega attempts fail me here
      . assumption
      . apply Nat.lt_of_lt_of_le
        . exact hidx
        . exact (bitblast.go aig lhs).property
      . assumption
      . apply Nat.lt_of_lt_of_le
        . exact hidx
        . apply Nat.le_trans
          . exact (bitblast.go aig lhs).property
          . exact (go (go aig lhs).1.aig rhs).property
      . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size
        apply Nat.lt_of_lt_of_le
        . exact hidx
        . apply Nat.le_trans
          . exact (bitblast.go aig lhs).property
          . exact (go (go aig lhs).1.aig rhs).property
  | un op expr ih =>
    cases op with
    | not =>
      dsimp [go]
      rw [Array.getElem?_lt, Array.getElem?_lt]
      rw [AIG.LawfulStreamOperator.decl_eq]
      rw [← Array.getElem?_lt, ← Array.getElem?_lt]
      rw [ih]
      . assumption
      . assumption
      . apply Nat.lt_of_lt_of_le
        . exact hidx
        . exact (go aig expr).property
      . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size
        apply Nat.lt_of_lt_of_le
        . exact hidx
        . exact (go aig expr).property

theorem bitblast.go_decl_eq (aig : AIG BVBit) (expr : BVExpr w)
    : ∀ (idx : Nat) (h1) (h2),
        (go aig expr).val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  have := go_decl_eq? aig expr idx h1
  rw [Array.getElem?_lt, Array.getElem?_lt] at this
  injection this

theorem bitblast_decl_eq (aig : AIG BVBit) (expr : BVExpr w)
    : ∀ (idx : Nat) (h1) (h2),
        (bitblast aig expr).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros
  unfold bitblast
  apply bitblast.go_decl_eq

instance : AIG.LawfulStreamOperator BVBit (fun _ w => BVExpr w) bitblast where
  le_size := by intros; apply bitblast_le_size
  decl_eq := by intros; apply bitblast_decl_eq

end BVExpr

namespace BVPred

structure ExprPair where
  {w : Nat}
  lhs : BVExpr w
  rhs : BVExpr w

def mkEq (aig : AIG BVBit) (pair : ExprPair) : AIG.Entrypoint BVBit :=
  match pair.lhs.bitblast aig with
  | ⟨laig, lhsRefs⟩ =>
    match hr:pair.rhs.bitblast laig with
    | ⟨raig, rhsRefs⟩ =>
      let lhsRefs := lhsRefs.cast <| by
        intro i hi
        have : raig = (pair.rhs.bitblast laig).aig := by
          simp [hr]
        rw [this]
        apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
        assumption
      let ⟨finalAig, bits⟩ := AIG.RefStream.zip raig ⟨lhsRefs, rhsRefs, AIG.mkBEqCached⟩
      AIG.RefStream.fold finalAig (.mkAnd bits)

theorem mkEq_le_size (aig : AIG BVBit) (target : ExprPair)
    : aig.decls.size ≤ (mkEq aig target).aig.decls.size := by
  unfold mkEq
  dsimp
  apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.RefStream.fold)
  apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.zip)
  apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
  apply AIG.LawfulStreamOperator.le_size (f := BVExpr.bitblast)

theorem mkEq_decl_eq (aig : AIG BVBit) (target : ExprPair) {h : idx < aig.decls.size} :
    have := mkEq_le_size aig target
    (mkEq aig target).aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  unfold mkEq
  dsimp
  rw [AIG.LawfulOperator.decl_eq]
  rw [AIG.LawfulStreamOperator.decl_eq]
  rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast)]
  rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast)]
  . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
    assumption
  . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
    apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
    assumption
  . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := AIG.RefStream.zip)
    apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
    apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
    assumption

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
