import LeanSAT.BitBlast.BVExpr.Basic
import LeanSAT.AIG
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Add
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.ShiftLeft
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Const

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
    let res := AIG.RefStream.ite aig ⟨rhs.get 0 (by assumption), lhs, zero⟩
    let aig := res.aig
    let acc := res.stream
    have := by
      apply AIG.LawfulStreamOperator.le_size (f := AIG.RefStream.ite)
    let lhs := lhs.cast this
    let rhs := rhs.cast this
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
      let res := AIG.RefStream.ite aig ⟨rhs.get curr h, added, acc⟩
      let aig := res.aig
      let acc := res.stream
      have := by apply AIG.LawfulStreamOperator.le_size (f := AIG.RefStream.ite)
      let lhs := lhs.cast this
      let rhs := rhs.cast this
      go aig (curr + 1) (by omega) acc lhs rhs
    else
      ⟨aig, acc⟩

namespace blastMul

theorem go_le_size {w : Nat} (aig : AIG BVBit) (curr : Nat) (hcurr : curr ≤ w) (acc : AIG.RefStream aig w)
      (lhs rhs : AIG.RefStream aig w)
    : aig.decls.size ≤ (go aig curr hcurr acc lhs rhs).aig.decls.size := by
  unfold go
  split
  . dsimp
    refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.ite)
    apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := blastAdd)
    apply AIG.LawfulStreamOperator.le_size (f := blastShiftLeftConst)
  . simp

theorem go_decl_eq {w : Nat} (aig : AIG BVBit) (curr : Nat) (hcurr : curr ≤ w) (acc : AIG.RefStream aig w)
      (lhs rhs : AIG.RefStream aig w)
    : ∀ (idx : Nat) (h1) (h2),
       (go aig curr hcurr acc lhs rhs).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig curr hcurr acc lhs rhs = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    rw [← hgo]
    intro idx h1 h2
    rw [go_decl_eq]
    rw [AIG.LawfulStreamOperator.decl_eq (f := AIG.RefStream.ite)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastAdd)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastShiftLeftConst)]
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastShiftLeftConst)
      assumption
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastAdd)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastShiftLeftConst)
      assumption
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := AIG.RefStream.ite)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastAdd)
      apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastShiftLeftConst)
      assumption
  . simp [← hgo]

end blastMul

instance : AIG.LawfulStreamOperator BVBit AIG.BinaryRefStream blastMul where
  le_size := by
    intros
    unfold blastMul
    split
    . simp
    . dsimp
      refine Nat.le_trans ?_ (by apply blastMul.go_le_size)
      apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.ite)
      apply AIG.LawfulStreamOperator.le_size (f := blastConst)
  decl_eq := by
    intros
    unfold blastMul
    split
    . simp
    . dsimp
      rw [blastMul.go_decl_eq]
      rw [AIG.LawfulStreamOperator.decl_eq (f := AIG.RefStream.ite)]
      rw [AIG.LawfulStreamOperator.decl_eq (f := blastConst)]
      . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastConst)
        assumption
      . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := AIG.RefStream.ite)
        apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastConst)
        assumption

end bitblast
end BVExpr
