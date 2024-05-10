import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.AIG

namespace BVExpr
namespace bitblast

def blastNot (aig : AIG BVBit) (s : AIG.RefStream aig w) : AIG.RefStreamEntry BVBit w :=
  AIG.RefStream.map aig ⟨s, AIG.mkNotCached⟩

instance : AIG.LawfulStreamOperator BVBit AIG.RefStream blastNot where
  le_size := by
    intros
    unfold blastNot
    apply AIG.LawfulStreamOperator.le_size (f := AIG.RefStream.map)
  decl_eq := by
    intros
    unfold blastNot
    apply AIG.LawfulStreamOperator.decl_eq (f := AIG.RefStream.map)

end bitblast
end BVExpr
