import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Neg
import LeanSAT.AIG

namespace BVExpr
namespace bitblast

def blastSub (aig : AIG BVBit) (input : AIG.BinaryRefStream aig w) : AIG.RefStreamEntry BVBit w :=
  let lhs := input.lhs
  let rhs := input.rhs
  let res := blastNeg aig rhs
  let aig := res.aig
  let negStream := res.stream
  let lhs := lhs.cast <| by
    simp (config := { zetaDelta := true }) only
    apply AIG.LawfulStreamOperator.le_size (f := blastNeg)
  blastAdd aig ⟨lhs, negStream⟩

instance : AIG.LawfulStreamOperator BVBit AIG.BinaryRefStream blastSub where
  le_size := by
    intros
    unfold blastSub
    dsimp
    apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := blastAdd)
    apply AIG.LawfulStreamOperator.le_size (f := blastNeg)
  decl_eq := by
    intros
    unfold blastSub
    dsimp
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastAdd)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastNeg)]
    apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastNeg)
    assumption

end bitblast
end BVExpr
