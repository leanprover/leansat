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

-- TODO: Idea for LawfulOperator refactor:
-- TODO: Currently LawfulOperator is only allowed to return Entrypoints. We could instead envision
-- parametrising it over some container that must contain at least an AIG. This would allow the
-- blastVar, blastConst and RefStream APIs to become part of LawfulOperator

namespace bitblast

def blastVar (w : Nat) (aig : AIG BVBit) (idx : Nat) (s : AIG.RefStream aig idx) (a : Nat)
    (hidx : idx ≤ w)
    : (aig : AIG BVBit) × AIG.RefStream aig w :=
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
      blastVar w newAig (idx + 1) s a (by omega)
  else
    have hidx : idx = w := by omega
    ⟨aig, hidx ▸ s⟩
termination_by w - idx

theorem blastVar_le_size {aig : AIG BVBit} (idx : Nat) (s : AIG.RefStream aig idx) (a : Nat)
    (hidx : idx ≤ w)
    : aig.decls.size ≤ (blastVar w aig idx s a hidx).1.decls.size := sorry

theorem blastVar_decl_eq? {aig : AIG BVBit} (i : Nat) (s : AIG.RefStream aig i) (a : Nat)
    (hi : i ≤ w)
    : ∀ (idx : Nat) (_hidx : idx < aig.decls.size),
        (blastVar w aig i s a hi).1.decls[idx]? = aig.decls[idx]? := sorry

theorem blastVar_decl_eq {aig : AIG BVBit} (i : Nat) (s : AIG.RefStream aig i) (a : Nat)
    (hi : i ≤ w)
    : ∀ (idx : Nat) (h1) (h2),
        (blastVar w aig i s a hi).1.decls[idx]'h2 = aig.decls[idx]'h1 := sorry

def blastConst {w : Nat} (aig : AIG BVBit) (idx : Nat) (s : AIG.RefStream aig idx) (val : BitVec w)
    (hidx : idx ≤ w)
    : (aig : AIG BVBit) × AIG.RefStream aig w :=
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
      blastConst newAig (idx + 1) s val (by omega)
  else
    have hidx : idx = w := by omega
    ⟨aig, hidx ▸ s⟩
termination_by w - idx

theorem blastConst_le_size {aig : AIG BVBit} (idx : Nat) (s : AIG.RefStream aig idx) (val : BitVec w)
    (hidx : idx ≤ w)
    : aig.decls.size ≤ (blastConst aig idx s val hidx).1.decls.size := sorry

theorem blastConst_decl_eq? {aig : AIG BVBit} (i : Nat) (s : AIG.RefStream aig i) (val : BitVec w)
    (hi : i ≤ w)
    : ∀ (idx : Nat) (_hidx : idx < aig.decls.size),
        (blastConst aig i s val hi).1.decls[idx]? = aig.decls[idx]? := sorry

theorem blastConst_decl_eq {aig : AIG BVBit} (i : Nat) (s : AIG.RefStream aig i) (val : BitVec w)
    (hi : i ≤ w)
    : ∀ (idx : Nat) (h1) (h2),
        (blastConst aig i s val hi).1.decls[idx]'h2 = aig.decls[idx]'h1 := sorry

end bitblast

def bitblast (aig : AIG BVBit) (expr : BVExpr w) :
    (newAig : AIG.ExtendingAIG aig) × AIG.RefStream newAig.val w :=
  match expr with
  | .var a =>
    match haig:bitblast.blastVar w aig 0 .empty a (by omega) with
    | ⟨newAig, s⟩ =>
      -- TODO: Think of a way to prettify these theorems
      ⟨
        ⟨
          newAig,
          by
            have : newAig = (bitblast.blastVar w aig 0 .empty a (by omega)).1 :=
              by simp [haig]
            rw [this]
            apply bitblast.blastVar_le_size
        ⟩,
        s
      ⟩
  | .const val =>
    match haig:bitblast.blastConst aig 0 .empty val (by omega) with
    | ⟨newAig, s⟩ =>
      ⟨
        ⟨
          newAig,
          by
            have : newAig = (bitblast.blastConst aig 0 .empty val (by omega)).1 := by
              simp [haig]
            rw [this]
            apply bitblast.blastConst_le_size
        ⟩,
        s
      ⟩
  | .bin lhs op rhs =>
    match op with
    | .and =>
      match bitblast aig lhs with
      | ⟨⟨laig, hlaig⟩, lhs⟩ =>
        match bitblast laig rhs with
        | ⟨⟨raig, hraig⟩, rhs⟩ =>
          let lhs := lhs.cast <| by
            intro i hi
            dsimp at hi
            omega
          match hfinal:AIG.RefStream.zip raig lhs rhs AIG.mkAndCached with
          | ⟨finalAig, s⟩ => 
            ⟨
              ⟨
                finalAig,
                by
                  have : finalAig = (AIG.RefStream.zip raig lhs rhs AIG.mkAndCached).1 := by
                    simp [hfinal]
                  rw [this]
                  refine Nat.le_trans ?_ (by apply AIG.RefStream.zip_le_size)
                  omega
              ⟩,
              s
            ⟩
  | .un op expr =>
    match op with
    | .not =>
      match bitblast aig expr with
      | ⟨⟨eaig, heaig⟩, estream⟩ => 
        match hfinal:estream.map eaig AIG.mkNotCached with
        | ⟨finalAig, s⟩ => 
          ⟨
            ⟨
              finalAig,
              by
                have : finalAig = (estream.map eaig AIG.mkNotCached).1 := by
                  simp [hfinal]
                rw [this]
                refine Nat.le_trans ?_ (by apply AIG.RefStream.map_le_size)
                omega
            ⟩,
            s
          ⟩

-- TODO: LawfulOperator style theorems for bitblast

end BVExpr

namespace BVPred

structure ExprPair where
  {w : Nat}
  lhs : BVExpr w
  rhs : BVExpr w

def mkEq (aig : AIG BVBit) (pair : ExprPair) : AIG.Entrypoint BVBit :=
  let ⟨⟨aig, hlaig⟩, lhsRefs⟩ := pair.lhs.bitblast aig
  let ⟨⟨aig, hraig⟩, rhsRefs⟩ := pair.rhs.bitblast aig
  let lhsRefs := lhsRefs.cast <| by
    intro i hi
    dsimp at hi
    omega
  let ⟨aig, bits⟩ := AIG.RefStream.zip aig lhsRefs rhsRefs AIG.mkBEqCached
  bits.fold aig AIG.mkAndCached

theorem mkEq_le_size (aig : AIG BVBit) (target : ExprPair)
    : aig.decls.size ≤ (mkEq aig target).aig.decls.size := by
  unfold mkEq
  sorry

theorem mkEq_decl_eq (aig : AIG BVBit) (target : ExprPair) {h : idx < aig.decls.size} :
    have := mkEq_le_size aig target
    (mkEq aig target).aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  unfold mkEq
  sorry

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
