import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Expr
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Carry

namespace BVPred

def mkUle (aig : AIG BVBit) (pair : ExprPair) : AIG.Entrypoint BVBit :=
  let res := pair.lhs.bitblast aig
  let aig := res.aig
  let lhsRefs := res.stream
  let res := BVExpr.bitblast.blastNot aig lhsRefs
  let aig := res.aig
  let lhsRefs := res.stream
  let res := pair.rhs.bitblast aig
  let aig := res.aig
  let rhsRefs := res.stream
  let res := aig.mkConstCached true
  let aig := res.aig
  let trueRef := res.ref
  let lhsRefs := lhsRefs.cast <| by
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkConstCached)
    apply AIG.LawfulStreamOperator.le_size (f := BVExpr.bitblast)
  let rhsRefs := rhsRefs.cast <| by
    apply AIG.LawfulOperator.le_size (f := AIG.mkConstCached)
  BVExpr.bitblast.mkOverflowBit aig ⟨_, ⟨rhsRefs, lhsRefs⟩, trueRef⟩

instance : AIG.LawfulOperator BVBit (fun _ => ExprPair) mkUle where
  le_size := by
    intros
    unfold mkUle
    dsimp
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.mkOverflowBit)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkConstCached)
    apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
    apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.blastNot)
    apply AIG.LawfulStreamOperator.le_size (f := BVExpr.bitblast)
  decl_eq := by
    intros
    unfold mkUle
    dsimp
    rw [AIG.LawfulOperator.decl_eq (f := BVExpr.bitblast.mkOverflowBit)]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast.blastNot)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast)]
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
      assumption
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast.blastNot)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
      assumption
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast.blastNot)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
      assumption
    . apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast.blastNot)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
      assumption

end BVPred
