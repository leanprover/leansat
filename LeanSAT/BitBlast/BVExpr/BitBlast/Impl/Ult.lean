/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Carry
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Not

namespace BVPred

variable [Hashable α] [DecidableEq α]

def mkUlt (aig : AIG α) (pair : AIG.BinaryRefStream aig w) : AIG.Entrypoint α :=
  let ⟨lhsRefs, rhsRefs⟩ := pair
  let res := BVExpr.bitblast.blastNot aig rhsRefs
  let aig := res.aig
  let rhsRefs := res.stream
  let res := aig.mkConstCached true
  let aig := res.aig
  let trueRef := res.ref
  let lhsRefs := lhsRefs.cast <| by
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkConstCached)
    apply AIG.LawfulStreamOperator.le_size (f := BVExpr.bitblast.blastNot)
  let rhsRefs := rhsRefs.cast <| by
    apply AIG.LawfulOperator.le_size (f := AIG.mkConstCached)
  let res := BVExpr.bitblast.mkOverflowBit aig ⟨_, ⟨lhsRefs, rhsRefs⟩, trueRef⟩
  let aig := res.aig
  let overflowRef := res.ref
  aig.mkNotCached overflowRef

instance {w : Nat} : AIG.LawfulOperator α (AIG.BinaryRefStream · w) mkUlt where
  le_size := by
    intros
    unfold mkUlt
    dsimp
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkNotCached)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.mkOverflowBit)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkConstCached)
    apply AIG.LawfulStreamOperator.le_size (f := BVExpr.bitblast.blastNot)
  decl_eq := by
    intros
    unfold mkUlt
    dsimp
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkNotCached)]
    rw [AIG.LawfulOperator.decl_eq (f := BVExpr.bitblast.mkOverflowBit)]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast.blastNot)]
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast.blastNot)
      assumption
    . apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast.blastNot)
      assumption
    . apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast.mkOverflowBit)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast.blastNot)
      assumption

end BVPred
