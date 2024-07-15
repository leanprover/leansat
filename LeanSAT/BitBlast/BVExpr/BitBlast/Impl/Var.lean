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
    let res := aig.mkAtomCached ⟨a, ⟨idx, hidx⟩⟩
    let aig := res.aig
    let bitRef := res.ref
    let s := s.cast <| by
      intros
      apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkAtomCached)
      omega
    let s := s.pushRef bitRef
    go w aig (idx + 1) s a (by omega)
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

theorem blastVar.go_decl_eq {aig : AIG BVBit} (i : Nat) (s : AIG.RefStream aig i) (a : Nat)
    (hi : i ≤ w)
    : ∀ (idx : Nat) (h1) (h2), (go w aig i s a hi).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go w aig i s a hi = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    rw [← hgo]
    intro idx h1 h2
    rw [blastVar.go_decl_eq]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkAtomCached)]
    apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkAtomCached)
    assumption
  . dsimp at hgo
    rw [← hgo]
    intros
    simp
termination_by w - i

theorem blastVar_decl_eq {aig : AIG BVBit} (var : BVVar w)
    : ∀ (idx : Nat) (h1) (h2), (blastVar aig var).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  unfold blastVar
  apply blastVar.go_decl_eq

instance : AIG.LawfulStreamOperator BVBit (fun _ w => BVVar w) blastVar where
  le_size := by intros; apply blastVar_le_size
  decl_eq := by intros; apply blastVar_decl_eq

end bitblast
end BVExpr
