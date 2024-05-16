import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Add
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Carry

open AIG

namespace BVExpr
namespace bitblast
namespace mkOverflowBit

theorem go_eq_carry (aig : AIG BVBit) (curr : Nat) (hcurr : curr ≤ w) (cin : Ref aig) (origCin : Ref aig)
    (lhs rhs : RefStream aig w) (lhsExpr rhsExpr : BVExpr w) (assign : Assignment)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, lhs.getRef idx hidx, assign.toAIGAssignment⟧ = (lhsExpr.eval assign).getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, rhs.getRef idx hidx, assign.toAIGAssignment⟧ = (rhsExpr.eval assign).getLsb idx)
    (hcin :
      ⟦aig, cin, assign.toAIGAssignment⟧
        =
      BitVec.carry curr (lhsExpr.eval assign) (rhsExpr.eval assign) ⟦aig, origCin, assign.toAIGAssignment⟧
    )
  : ⟦go aig curr hcurr cin lhs rhs, assign.toAIGAssignment⟧
      =
    BitVec.carry w (lhsExpr.eval assign) (rhsExpr.eval assign) ⟦aig, origCin, assign.toAIGAssignment⟧ := by
  unfold go
  dsimp
  split
  . rw [go_eq_carry]
    . congr 1
      rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderCarry)]
    . intros
      rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderCarry)]
      . simp [hleft]
      . simp [Ref.hgate]
    . intros
      rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderCarry)]
      . simp [hright]
      . simp [Ref.hgate]
    . simp [BitVec.carry_succ]
      rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderCarry)]
      rw [hleft, hright, hcin]
      rw [Bool.atLeastTwo_eq_halfAdder]
  . have : w = curr := by omega
    rw [hcin]
    simp [this]
termination_by w - curr

end mkOverflowBit

theorem mkOverflowBit_eq_carry (aig : AIG BVBit) (input : OverflowInput aig) (lhs rhs : BVExpr input.w)
    (assign : Assignment)
    (hleft : ∀ (idx : Nat) (hidx : idx < input.w), ⟦aig, input.stream.lhs.getRef idx hidx, assign.toAIGAssignment⟧ = (lhs.eval assign).getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < input.w), ⟦aig, input.stream.rhs.getRef idx hidx, assign.toAIGAssignment⟧ = (rhs.eval assign).getLsb idx)
  : ⟦mkOverflowBit aig input, assign.toAIGAssignment⟧
      =
    BitVec.carry input.w (lhs.eval assign) (rhs.eval assign) ⟦aig, input.cin, assign.toAIGAssignment⟧ := by
  unfold mkOverflowBit
  dsimp
  apply mkOverflowBit.go_eq_carry
  . assumption
  . assumption
  . simp [BitVec.carry_zero]

end bitblast
end BVExpr
