import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.AIG

namespace BVExpr
namespace bitblast

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
          apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkConstCached)
          omega
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
end BVExpr
