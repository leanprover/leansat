import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Eq
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Neq

namespace BVPred

def bitblast (aig : AIG BVBit) (pred : BVPred) : AIG.Entrypoint BVBit :=
  match pred with
  | .bin lhs op rhs =>
    match op with
    | .eq => mkEq aig ⟨lhs, rhs⟩
    | .neq => mkNeq aig ⟨lhs, rhs⟩

theorem bitblast_le_size (aig : AIG BVBit) (pred : BVPred)
    : aig.decls.size ≤ (bitblast aig pred).aig.decls.size := by
  cases pred with
  | bin lhs op rhs =>
    cases op with
    | eq =>
      simp only [bitblast]
      apply AIG.LawfulOperator.le_size
    | neq =>
      simp only [bitblast]
      apply AIG.LawfulOperator.le_size

theorem bitblast_decl_eq (aig : AIG BVBit) (pred : BVPred) {h : idx < aig.decls.size} :
    have := bitblast_le_size aig pred
    (bitblast aig pred).aig.decls[idx]'(by omega) = aig.decls[idx]'h := by
  cases pred with
  | bin lhs op rhs =>
    cases op with
    | eq =>
      simp only [bitblast]
      rw [AIG.LawfulOperator.decl_eq (f := mkEq)]
    | neq =>
      simp only [bitblast]
      rw [AIG.LawfulOperator.decl_eq (f := mkNeq)]

instance : AIG.LawfulOperator BVBit (fun _ => BVPred) bitblast where
  le_size := bitblast_le_size
  decl_eq := by intros; apply bitblast_decl_eq

end BVPred
