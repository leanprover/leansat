/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Add
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Carry

open AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace mkOverflowBit

theorem go_eq_carry (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (cin : Ref aig) (origCin : Ref aig)
    (lhs rhs : RefStream aig w) (lhsExpr rhsExpr : BitVec w) (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, lhs.getRef idx hidx, assign⟧ = lhsExpr.getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, rhs.getRef idx hidx, assign⟧ = rhsExpr.getLsb idx)
    (hcin :
      ⟦aig, cin, assign⟧
        =
      BitVec.carry curr lhsExpr rhsExpr ⟦aig, origCin, assign⟧
    )
  : ⟦go aig curr hcurr cin lhs rhs, assign⟧
      =
    BitVec.carry w lhsExpr rhsExpr ⟦aig, origCin, assign⟧ := by
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

theorem mkOverflowBit_eq_carry (aig : AIG α) (input : OverflowInput aig) (lhs rhs : BitVec input.w)
    (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < input.w), ⟦aig, input.stream.lhs.getRef idx hidx, assign⟧ = lhs.getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < input.w), ⟦aig, input.stream.rhs.getRef idx hidx, assign⟧ = rhs.getLsb idx)
  : ⟦mkOverflowBit aig input, assign⟧
      =
    BitVec.carry input.w lhs rhs ⟦aig, input.cin, assign⟧ := by
  unfold mkOverflowBit
  dsimp
  apply mkOverflowBit.go_eq_carry
  . assumption
  . assumption
  . simp [BitVec.carry_zero]

end bitblast
end BVExpr
