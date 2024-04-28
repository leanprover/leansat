import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Add

open AIG

namespace BVExpr
namespace bitblast
namespace blastAdd

@[simp]
theorem denote_mkFullAdderOut (assign : Assignment) (aig : AIG BVBit) (input : FullAdderInput aig)
    : ⟦mkFullAdderOut aig input, assign.toAIGAssignment⟧
        =
      xor
        (xor
           ⟦aig, input.lhs, assign.toAIGAssignment⟧
           ⟦aig, input.rhs, assign.toAIGAssignment⟧)
        ⟦aig, input.cin, assign.toAIGAssignment⟧
    := by
  simp only [mkFullAdderOut, Ref_cast', denote_mkXorCached, denote_projected_entry, Bool.bne_assoc,
    Bool.bne_left_inj]
  rw [LawfulOperator.denote_mem_prefix (f := mkXorCached)]

@[simp]
theorem denote_mkFullAdderCarry (assign : Assignment) (aig : AIG BVBit) (input : FullAdderInput aig)
    : ⟦mkFullAdderCarry aig input, assign.toAIGAssignment⟧
        =
       or
         (and
           (xor
             ⟦aig, input.lhs, assign.toAIGAssignment⟧
             ⟦aig, input.rhs, assign.toAIGAssignment⟧)
           ⟦aig, input.cin, assign.toAIGAssignment⟧)
         (and
           ⟦aig, input.lhs, assign.toAIGAssignment⟧
           ⟦aig, input.rhs, assign.toAIGAssignment⟧)
    := by
  simp only [mkFullAdderCarry, Ref_cast', Int.reduceNeg, denote_mkOrCached,
    LawfulOperator.denote_input_entry, denote_mkAndCached, denote_projected_entry',
    denote_mkXorCached, denote_projected_entry]
  -- Without conv mode this timeouts
  conv =>
    lhs
    lhs
    rhs
    rw [LawfulOperator.denote_mem_prefix (f := mkXorCached) (h := input.cin.hgate)]
  conv =>
    lhs
    rhs
    lhs
    rw [LawfulOperator.denote_mem_prefix (f := mkAndCached)]
    rw [LawfulOperator.denote_mem_prefix (f := mkXorCached) (h := input.lhs.hgate)]
  conv =>
    lhs
    rhs
    rhs
    rw [LawfulOperator.denote_mem_prefix (f := mkAndCached)]
    rw [LawfulOperator.denote_mem_prefix (f := mkXorCached) (h := input.rhs.hgate)]

-- TODO: additional assumption about cin
-- Proof idea: show that go always pulls through something that is equiv to BitVec.carry at the
-- next idx. In particular assuming that the thing it was given was BitVec.carry at the current
theorem go_eq_eval_getLsb (aig : AIG BVBit) (curr : Nat) (hcurr : curr ≤ w) (cin : Ref aig)
    (s : AIG.RefStream aig curr) (lhs rhs : AIG.RefStream aig w) (assign : Assignment)
    (lhsExpr rhsExpr : BVExpr w)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, lhs.getRef idx hidx, assign.toAIGAssignment⟧ = (lhsExpr.eval assign).getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, rhs.getRef idx hidx, assign.toAIGAssignment⟧ = (rhsExpr.eval assign).getLsb idx)
    (hcin :
      ⟦aig, cin, assign.toAIGAssignment⟧
        =
      BitVec.carry curr (lhsExpr.eval assign) (rhsExpr.eval assign) false
    )
  : ∀ (idx : Nat) (hidx1 : idx < w) (hidx2 : curr ≤ idx),
      ⟦
        (go aig curr hcurr cin s lhs rhs).aig,
        (go aig curr hcurr cin s lhs rhs).stream.getRef idx hidx1,
        assign.toAIGAssignment
      ⟧
        =
      ⟦aig, lhs.getRef idx hidx1, assign.toAIGAssignment⟧.xor
        (⟦aig, rhs.getRef idx hidx1, assign.toAIGAssignment⟧.xor
          (BitVec.carry idx (lhsExpr.eval assign) (rhsExpr.eval assign) false)) := by
  intro idx hidx1 hidx2
  generalize hgo : go aig curr hcurr cin s lhs rhs = res
  unfold go at hgo
  sorry

end blastAdd

theorem blastAdd_eq_eval_getLsb (aig : AIG BVBit) (lhs rhs : BVExpr w) (assign : Assignment)
      (input : BinaryRefStream aig w)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.getRef idx hidx, assign.toAIGAssignment⟧ = (lhs.eval assign).getLsb idx)
      (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.getRef idx hidx, assign.toAIGAssignment⟧ = (rhs.eval assign).getLsb idx)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastAdd aig input).aig, (blastAdd aig input).stream.getRef idx hidx, assign.toAIGAssignment⟧
          =
        (lhs.eval assign + rhs.eval assign).getLsb idx := by
  intro idx hidx
  rw [BitVec.getLsb_add]
  . rw [← hleft idx hidx]
    rw [← hright idx hidx]
    unfold blastAdd
    dsimp
    rw [blastAdd.go_eq_eval_getLsb _ 0 (by omega) _ _ _ _ assign lhs rhs _ _]
    . -- TODO: API lemmas
      simp [BinaryRefStream.cast]
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
    . simp
    . omega
    . intros
      -- TODO: API lemmas
      simp [BinaryRefStream.cast]
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      rw [hleft]
    . intros
      -- TODO: API lemmas
      simp [BinaryRefStream.cast]
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      rw [hright]
  . assumption

end bitblast
end BVExpr
