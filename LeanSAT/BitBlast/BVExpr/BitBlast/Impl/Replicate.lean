/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.Basic
import LeanSAT.AIG.LawfulStreamOperator

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

structure ReplicateTarget (aig : AIG α) (combined : Nat) where
  {w : Nat}
  n : Nat
  inner : AIG.RefStream aig w
  h : combined = w * n

def blastReplicate (aig : AIG α) (target : ReplicateTarget aig newWidth)
    : AIG.RefStreamEntry α newWidth :=
  let ⟨n, inner, h⟩ := target
  let ref := go n 0 (by omega) inner .empty
  ⟨aig, h ▸ ref⟩
where
  go {aig : AIG α} {w : Nat} (n : Nat) (curr : Nat) (hcurr : curr ≤ n) (input : AIG.RefStream aig w)
      (s : AIG.RefStream aig (w * curr)) : AIG.RefStream aig (w * n) :=
    if h : curr < n then
      let s := s.append input
      go n (curr + 1) (by omega) input s
    else
      have : curr = n := by omega
      this ▸ s
  termination_by n - curr

instance : AIG.LawfulStreamOperator α ReplicateTarget blastReplicate where
  le_size := by simp [blastReplicate]
  decl_eq := by simp [blastReplicate]

end bitblast
end BVExpr
