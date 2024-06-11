import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Eq
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Ult
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.GetLsb
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Expr
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Pred

open AIG

namespace BVPred

@[simp]
theorem bitblast_denote_eq_eval (aig : AIG BVBit) (pred : BVPred) (assign : BVExpr.Assignment)
    : ⟦bitblast aig pred, assign.toAIGAssignment⟧
        =
      pred.eval assign := by
  cases pred with
  | bin lhs op rhs =>
    cases op with
    | eq =>
      simp only [bitblast, eval_bin, BVBinPred.eval_eq]
      rw [mkEq_denote_eq_eval_beq]
      . intros
        rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := BVExpr.bitblast)]
        . simp
          rw [BVExpr.bitblast_denote_eq_eval_getLsb]
        . simp [Ref.hgate]
      . intros
        simp
    | ult =>
      simp only [bitblast, eval_bin, BVBinPred.eval_ult]
      rw [mkUlt_denote_eq_eval_ult]
      . intros
        rw [AIG.LawfulStreamOperator.denote_mem_prefix (f := BVExpr.bitblast)]
        . simp
          rw [BVExpr.bitblast_denote_eq_eval_getLsb]
        . simp [Ref.hgate]
      . intros
        simp
  | getLsb expr idx =>
    simp [bitblast]
    apply BitVec.lt_of_getLsb

end BVPred
