/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.Basic
import LeanSAT.AIG.CachedGatesLemmas
import LeanSAT.AIG.LawfulStreamOperator

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastConst (aig : AIG α) (val : BitVec w) : AIG.RefStreamEntry α w :=
  go aig 0 .empty val (by omega)
where
  go {w : Nat} (aig : AIG α) (idx : Nat) (s : AIG.RefStream aig idx) (val : BitVec w)
      (hidx : idx ≤ w)
      : AIG.RefStreamEntry α w :=
    if hidx:idx < w then
      let res := aig.mkConstCached (val.getLsb idx)
      let aig := res.aig
      let bitRef := res.ref
      let s := s.cast <| by
        intros
        apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkConstCached)
        omega
      let s := s.pushRef bitRef
      go aig (idx + 1) s val (by omega)
    else
      have hidx : idx = w := by omega
      ⟨aig, hidx ▸ s⟩
  termination_by w - idx

theorem blastConst.go_le_size {aig : AIG α} (idx : Nat) (s : AIG.RefStream aig idx) (val : BitVec w)
    (hidx : idx ≤ w)
    : aig.decls.size ≤ (go aig idx s val hidx).aig.decls.size := by
  unfold go
  split
  . dsimp
    refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulOperator.le_size
  . simp
termination_by w - idx

theorem blastConst_le_size {aig : AIG α} (val : BitVec w)
    : aig.decls.size ≤ (blastConst aig val).aig.decls.size := by
  unfold blastConst
  apply blastConst.go_le_size

theorem blastConst.go_decl_eq {aig : AIG α} (i : Nat) (s : AIG.RefStream aig i) (val : BitVec w)
    (hi : i ≤ w)
    : ∀ (idx : Nat) (h1) (h2),
        (go aig i s val hi).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig i s val hi = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    rw [← hgo]
    intro idx h1 h2
    rw [blastConst.go_decl_eq]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
    apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
    assumption
  . dsimp at hgo
    rw [← hgo]
    intros
    simp
termination_by w - i

theorem blastConst_decl_eq {aig : AIG α} (val : BitVec w)
    : ∀ (idx : Nat) (h1) (h2),
        (blastConst aig val).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros
  unfold blastConst
  apply blastConst.go_decl_eq

instance : AIG.LawfulStreamOperator α (fun _ w => BitVec w) blastConst where
  le_size := by intros; apply blastConst_le_size
  decl_eq := by intros; apply blastConst_decl_eq


end bitblast
end BVExpr
