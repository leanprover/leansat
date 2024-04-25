import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Expr
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Eq

namespace BVPred

def mkNeq (aig : AIG BVBit) (pair : ExprPair) : AIG.Entrypoint BVBit :=
  let ⟨aig, gate, hgate⟩ := mkEq aig pair
  aig.mkNotCached (AIG.Ref.mk gate hgate)

theorem mkNeq_le_size (aig : AIG BVBit) (target : ExprPair)
    : aig.decls.size ≤ (mkNeq aig target).aig.decls.size := by
  unfold mkNeq
  dsimp
  apply AIG.LawfulOperator.le_size_of_le_aig_size
  apply AIG.LawfulOperator.le_size

theorem mkNeq_decl_eq (aig : AIG BVBit) (target : ExprPair) {h : idx < aig.decls.size} :
    have := mkNeq_le_size aig target
    (mkNeq aig target).aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  unfold mkNeq
  dsimp
  rw [AIG.LawfulOperator.decl_eq]
  rw [AIG.LawfulOperator.decl_eq (f := mkEq)]
  apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := mkEq)
  assumption

instance : AIG.LawfulOperator BVBit (fun _ => ExprPair) mkNeq where
  le_size := mkNeq_le_size
  decl_eq := by intros; apply mkNeq_decl_eq

end BVPred
