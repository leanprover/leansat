import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Const
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Not
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Add
import LeanSAT.AIG

namespace BVExpr
namespace bitblast

open BitVec

def blastNeg (aig : AIG BVBit) (s : AIG.RefStream aig w) : AIG.RefStreamEntry BVBit w :=
  let res := blastNot aig s
  let aig := res.aig
  let notStream := res.stream
  let res := blastConst aig 1#w
  let aig := res.aig
  let oneStream := res.stream
  let notStream := notStream.cast <| by
    simp (config := { zetaDelta := true }) only
    apply AIG.LawfulStreamOperator.le_size (f := blastConst)
  blastAdd aig ⟨notStream, oneStream⟩

instance : AIG.LawfulStreamOperator BVBit AIG.RefStream blastNeg where
  le_size := by
    intros
    unfold blastNeg
    dsimp
    apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := blastAdd)
    apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := blastConst)
    apply AIG.LawfulStreamOperator.le_size (f := blastNot)
  decl_eq := by
    intros
    unfold blastNeg
    dsimp
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastAdd)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastConst)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastNot)]
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastNot)
      assumption
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastConst)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastNot)
      assumption

end bitblast
end BVExpr

