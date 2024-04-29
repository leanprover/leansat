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
  rw [LawfulOperator.denote_mem_prefix (f := mkXorCached) (h := input.cin.hgate)]
  rw [LawfulOperator.denote_mem_prefix (f := mkAndCached)]
  rw [LawfulOperator.denote_mem_prefix (f := mkXorCached) (h := input.lhs.hgate)]
  rw [LawfulOperator.denote_mem_prefix (f := mkAndCached)]
  rw [LawfulOperator.denote_mem_prefix (f := mkXorCached) (h := input.rhs.hgate)]

theorem mkFullAdder_denote_mem_prefix (aig : AIG BVBit) (input : FullAdderInput aig) (start : Nat)
    (hstart)
  : ⟦
      (mkFullAdder aig input).aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply FullAdderOutput.hle⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign⟧ := by
  unfold mkFullAdder
  dsimp
  rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderCarry)]
  rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderOut)]

theorem go_denote_mem_prefix (aig : AIG BVBit) (curr : Nat) (hcurr : curr ≤ w) (cin : Ref aig)
    (s : AIG.RefStream aig curr) (lhs rhs : AIG.RefStream aig w) (start : Nat) (hstart)
  : ⟦
      (go aig curr hcurr cin s lhs rhs).aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply go_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign⟧ := by
  apply denote.eq_of_aig_eq (entry := ⟨aig, start,hstart⟩)
  apply IsPrefix.of
  . intros
    apply go_decl_eq
  . intros
    apply go_le_size

theorem go_getRef_aux (aig : AIG BVBit) (curr : Nat) (hcurr : curr ≤ w) (cin : Ref aig)
    (s : AIG.RefStream aig curr) (lhs rhs : AIG.RefStream aig w)
    -- The hfoo here is a trick to make the dependent type gods happy
    : ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig curr hcurr cin s lhs rhs).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig curr hcurr cin s lhs rhs = res
  unfold go at hgo
  dsimp at hgo
  split at hgo
  . rw [← hgo]
    intro hfoo
    rw [go_getRef_aux]
    rw [AIG.RefStream.getRef_push_ref_lt]
    . simp only [Ref.cast, Ref.mk.injEq]
      rw [AIG.RefStream.getRef_cast]
      . simp
      . assumption
    . apply go_le_size
  . rw [← hgo]
    simp only [Nat.le_refl, RefStream.getRef, Ref_cast', Ref.mk.injEq, true_implies]
    congr
    . omega
    . simp
termination_by w - curr

theorem go_getRef (aig : AIG BVBit) (curr : Nat) (hcurr : curr ≤ w) (cin : Ref aig)
    (s : AIG.RefStream aig curr) (lhs rhs : AIG.RefStream aig w)
    : ∀ (idx : Nat) (hidx : idx < curr),
        (go aig curr hcurr cin s lhs rhs).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_getRef_aux

theorem _root_.Bool.atLeastTwo_eq_halfAdder (lhsBit rhsBit carry : Bool)
  : Bool.atLeastTwo lhsBit rhsBit carry
      =
    (((xor lhsBit rhsBit) && carry) || (lhsBit && rhsBit)) := by
  cases lhsBit <;> cases rhsBit <;> cases carry <;> decide

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
  dsimp at hgo
  split at hgo
  . next hlt =>
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      rw [← hgo]
      rw [go_getRef (hidx := by omega)]
      rw [AIG.RefStream.getRef_push_ref_eq' (hidx := by rw [heq])]
      simp only [← heq]
      rw [go_denote_mem_prefix]
      . unfold mkFullAdder
        simp [hcin]
      . simp only [Ref_cast']
        apply Ref.hgate
    | inr hlt =>
      rw [← hgo]
      rw [go_eq_eval_getLsb (lhsExpr := lhsExpr) (rhsExpr := rhsExpr) (curr := curr + 1)]
      . rw [mkFullAdder_denote_mem_prefix]
        rw [mkFullAdder_denote_mem_prefix]
        . simp
        . simp [Ref.hgate]
        . simp [Ref.hgate]
      . intro idx hidx
        rw [mkFullAdder_denote_mem_prefix]
        rw [← hleft idx hidx]
        . simp
        . simp [Ref.hgate]
      . intro idx hidx
        rw [mkFullAdder_denote_mem_prefix]
        rw [← hright idx hidx]
        . simp
        . simp [Ref.hgate]
      . unfold mkFullAdder
        simp only [Ref_cast', id_eq, Int.reduceNeg, denote_projected_entry, denote_mkFullAdderCarry,
          FullAdderInput.lhs_cast, FullAdderInput.rhs_cast, FullAdderInput.cin_cast,
          BitVec.carry_succ]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderOut)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderOut)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderOut)]
        rw [hleft, hright, hcin]
        simp [_root_.Bool.atLeastTwo_eq_halfAdder]
      . omega
  . omega
termination_by w - curr

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
    . simp only [BinaryRefStream.lhs_getRef_cast, Ref_cast', BinaryRefStream.rhs_getRef_cast]
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
    . simp
    . omega
    . intros
      simp only [BinaryRefStream.lhs_getRef_cast, Ref_cast']
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      rw [hleft]
    . intros
      simp only [BinaryRefStream.rhs_getRef_cast, Ref_cast']
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      rw [hright]
  . assumption

end bitblast
end BVExpr
