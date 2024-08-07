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

def blastRotateRight (aig : AIG α) (target : AIG.ShiftTarget aig w)
    : AIG.RefStreamEntry α w :=
  let ⟨input, distance⟩ := target
  ⟨aig, go input distance 0 (by omega) .empty⟩
where
  go {aig : AIG α} (input : AIG.RefStream aig w) (distance : Nat) (curr : Nat) (hcurr : curr ≤ w)
      (s : AIG.RefStream aig curr)
    : AIG.RefStream aig w :=
  if hcurr1:curr < w then
    if hcurr2:curr < w - distance % w then
      let ref := input.getRef ((distance % w) + curr) (by omega)
      let s := s.pushRef ref
      go input distance (curr + 1) (by omega) s
    else
      let ref := input.getRef (curr - (w - (distance % w))) (by omega)
      let s := s.pushRef ref
      go input distance (curr + 1) (by omega) s
  else
    have hcurr : curr = w := by omega
    hcurr ▸ s
termination_by w - curr

instance : AIG.LawfulStreamOperator α AIG.ShiftTarget blastRotateRight where
  le_size := by
    intros
    unfold blastRotateRight
    dsimp
    omega
  decl_eq := by
    intros
    unfold blastRotateRight
    dsimp

end bitblast
end BVExpr
