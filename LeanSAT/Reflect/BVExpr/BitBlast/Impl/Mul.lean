import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.AIG
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Add
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.ShiftLeft
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Const

namespace BVExpr
namespace bitblast

def blastMul (aig : AIG BVBit) (input : AIG.BinaryRefStream aig w) : AIG.RefStreamEntry BVBit w :=
  if h : w = 0 then
    ⟨aig, h ▸ .empty⟩
  else
    /-
    theorem mulRec_zero_eq (l r : BitVec w) :
        mulRec l r 0 = if r.getLsb 0 then l else 0 := by
    -/
    have : 0 < w := by omega
    let res := blastConst aig 0
    let aig := res.aig
    let zero := res.stream
    have := by
      apply AIG.LawfulStreamOperator.le_size (f := blastConst)
    let input := input.cast this
    let ⟨lhs, rhs⟩ := input
    let res := AIG.RefStream.ite aig ⟨rhs.getRef 0 (by assumption), lhs, zero⟩
    let aig := res.aig
    let acc := res.stream
    have := by
      apply AIG.LawfulStreamOperator.le_size (f := AIG.RefStream.ite)
    let lhs := lhs.cast this
    let rhs := rhs.cast this
    -- TODO: Figure out if starting at 1 here is indeed correct
    go aig 1 (by omega) acc lhs rhs
where
  go {w : Nat} (aig : AIG BVBit) (curr : Nat) (hcurr : curr ≤ w) (acc : AIG.RefStream aig w)
      (lhs rhs : AIG.RefStream aig w)
      : AIG.RefStreamEntry BVBit w :=
    if h:curr < w then
      /-
      theorem mulRec_succ_eq (l r : BitVec w) (s : Nat) :
          mulRec l r (s + 1) = mulRec l r s + if r.getLsb (s + 1) then (l <<< (s + 1)) else 0
      -/
      let res := blastShiftLeftConst aig ⟨lhs, curr⟩
      let aig := res.aig
      let shifted := res.stream
      have := by apply AIG.LawfulStreamOperator.le_size (f := blastShiftLeftConst)
      let lhs := lhs.cast this
      let rhs := rhs.cast this
      let acc := acc.cast this
      let res := blastAdd aig ⟨acc, shifted⟩
      let aig := res.aig
      let added := res.stream
      have := by apply AIG.LawfulStreamOperator.le_size (f := blastAdd)
      let lhs := lhs.cast this
      let rhs := rhs.cast this
      let acc := acc.cast this
      let res := AIG.RefStream.ite aig ⟨rhs.getRef curr h, added, acc⟩
      let aig := res.aig
      let acc := res.stream
      have := by apply AIG.LawfulStreamOperator.le_size (f := AIG.RefStream.ite)
      let lhs := lhs.cast this
      let rhs := rhs.cast this
      go aig (curr + 1) (by omega) acc lhs rhs
    else
      have : curr = w := by omega
      ⟨aig, this ▸ acc⟩

instance : AIG.LawfulStreamOperator BVBit AIG.BinaryRefStream blastMul where
  le_size := sorry
  decl_eq := sorry

end bitblast
end BVExpr
