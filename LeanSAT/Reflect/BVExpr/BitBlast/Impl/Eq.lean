import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Expr

namespace BVPred

def mkEq (aig : AIG BVBit) (pair : ExprPair) : AIG.Entrypoint BVBit :=
  let res := pair.lhs.bitblast aig
  let aig := res.aig
  let lhsRefs := res.stream
  let res := pair.rhs.bitblast aig
  let aig := res.aig
  let rhsRefs := res.stream
  let lhsRefs := lhsRefs.cast <| by
    simp (config := { zetaDelta := true }) only
    apply AIG.LawfulStreamOperator.le_size (f := BVExpr.bitblast)
  streamProc aig ⟨lhsRefs, rhsRefs⟩
where
  streamProc {w : Nat} (aig : AIG BVBit) (input : AIG.BinaryRefStream aig w) : AIG.Entrypoint BVBit :=
    let res := AIG.RefStream.zip aig ⟨input, AIG.mkBEqCached⟩
    let aig := res.aig
    let bits := res.stream
    AIG.RefStream.fold aig (.mkAnd bits)

instance {w : Nat} : AIG.LawfulOperator BVBit (AIG.BinaryRefStream · w) mkEq.streamProc where
  le_size := by
    intros
    unfold mkEq.streamProc
    dsimp
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.RefStream.fold)
    apply AIG.LawfulStreamOperator.le_size (f := AIG.RefStream.zip)
  decl_eq := by
    intros
    unfold mkEq.streamProc
    dsimp
    rw [AIG.LawfulOperator.decl_eq (f := AIG.RefStream.fold)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := AIG.RefStream.zip)]
    apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := AIG.RefStream.zip)
    assumption

instance : AIG.LawfulOperator BVBit (fun _ => ExprPair) mkEq where
  le_size := by
    intros
    unfold mkEq
    dsimp
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := mkEq.streamProc)
    apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
    apply AIG.LawfulStreamOperator.le_size (f := BVExpr.bitblast)
  decl_eq := by
    intros
    unfold mkEq
    dsimp
    rw [AIG.LawfulOperator.decl_eq (f := mkEq.streamProc)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast)]
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
      assumption
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
      assumption


end BVPred
