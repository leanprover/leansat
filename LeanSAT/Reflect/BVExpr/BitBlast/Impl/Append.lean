import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.AIG

namespace BVExpr
namespace bitblast

structure AppendTarget (aig : AIG BVBit) (combined : Nat) where
  {lw : Nat}
  {rw : Nat}
  lhs : AIG.RefStream aig lw
  rhs : AIG.RefStream aig rw
  h : combined = rw + lw

def blastAppend (aig : AIG BVBit) (target : AppendTarget aig newWidth)
    : AIG.RefStreamEntry BVBit newWidth :=
  let ⟨lhs, rhs, h⟩ := target
  let combined := rhs.append lhs
  ⟨aig, h ▸ combined⟩

instance : AIG.LawfulStreamOperator BVBit AppendTarget blastAppend where
  le_size := by simp [blastAppend]
  decl_eq := by simp [blastAppend]

end bitblast
end BVExpr
