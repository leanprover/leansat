import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Expr

namespace BVPred

def mkEq (aig : AIG BVBit) (pair : ExprPair) : AIG.Entrypoint BVBit :=
  match pair.lhs.bitblast aig with
  | ⟨laig, lhsRefs⟩ =>
    match hr:pair.rhs.bitblast laig with
    | ⟨raig, rhsRefs⟩ =>
      let lhsRefs := lhsRefs.cast <| by
        have : raig = (pair.rhs.bitblast laig).aig := by
          simp [hr]
        rw [this]
        apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
        omega
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

end BVPred
