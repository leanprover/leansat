/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Add

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

structure OverflowInput (aig : AIG α) where
  (w : Nat)
  stream : AIG.BinaryRefStream aig w
  cin : AIG.Ref aig

def mkOverflowBit (aig : AIG α) (input : OverflowInput aig) : AIG.Entrypoint α :=
  let ⟨_, ⟨lhs, rhs⟩, cin⟩ := input
  go aig 0 (by omega) cin lhs rhs
where
  go {w : Nat} (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (cin : AIG.Ref aig)
      (lhs rhs : AIG.RefStream aig w)
      : AIG.Entrypoint α :=
    if hidx:curr < w then
      let lin := lhs.get curr hidx
      let rin := rhs.get curr hidx
      let res := mkFullAdderCarry aig ⟨lin, rin, cin⟩
      have := by
        apply AIG.LawfulOperator.le_size (f := mkFullAdderCarry)
      let aig := res.aig
      let carryRef := res.ref
      let lhs := lhs.cast this
      let rhs := rhs.cast this
      go aig (curr + 1) (by omega) carryRef lhs rhs
    else
      ⟨aig, cin⟩
  termination_by w - curr

namespace mkOverflowBit

theorem go_le_size {aig : AIG α} {cin} {lhs rhs : AIG.RefStream aig w}
    : aig.decls.size ≤ (go aig curr hcurr cin lhs rhs).aig.decls.size := by
  unfold go
  dsimp
  split
  . refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulOperator.le_size (f := mkFullAdderCarry)
  . dsimp
    omega
termination_by w - curr

theorem go_decl_eq {aig : AIG α} {cin} {lhs rhs : AIG.RefStream aig w}
    : ∀ (idx : Nat) (h1) (h2),
        (go aig curr hcurr cin lhs rhs).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig curr hcurr cin lhs rhs = res
  unfold go at hgo
  dsimp at hgo
  split at hgo
  . rw [← hgo]
    intros
    rw [go_decl_eq]
    rw [AIG.LawfulOperator.decl_eq (f := mkFullAdderCarry)]
    apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := mkFullAdderCarry)
    assumption
  . simp [← hgo]
termination_by w - curr

instance : AIG.LawfulOperator α OverflowInput mkOverflowBit where
  le_size := by
    intros
    unfold mkOverflowBit
    dsimp
    apply go_le_size
  decl_eq := by
    intros
    unfold mkOverflowBit
    dsimp
    rw [go_decl_eq]

end mkOverflowBit

end bitblast
end BVExpr
