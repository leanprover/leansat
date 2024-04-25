import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.ShiftLeft

open AIG

namespace BVExpr
namespace bitblast
namespace blastShiftLeft

theorem go_getRef_aux (aig : AIG BVBit) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig input distance curr hcurr s).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig input distance curr hcurr s = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    split at hgo
    . rw [← hgo]
      intros
      rw [go_getRef_aux]
      rw [AIG.RefStream.getRef_push_ref_lt]
      . simp only [Ref.cast, Ref.mk.injEq]
        rw [AIG.RefStream.getRef_cast]
        . simp
        . assumption
      . apply go_le_size
    . rw [← hgo]
      intros
      rw [go_getRef_aux]
      rw [AIG.RefStream.getRef_push_ref_lt]
  . dsimp at hgo
    rw [← hgo]
    simp only [Nat.le_refl, RefStream.getRef, Ref_cast', Ref.mk.injEq, true_implies]
    congr
    . omega
    . simp
termination_by w - curr

theorem go_getRef (aig : AIG BVBit) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx : idx < curr),
        (go aig input distance curr hcurr s).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_getRef_aux

theorem go_denote_mem_prefix (aig : AIG BVBit) (distance : Nat) (input : AIG.RefStream aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr) (start : Nat) (hstart)
  : ⟦
      (go aig input distance curr hcurr s).aig,
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

theorem go_eq_eval_getLsb (aig : AIG BVBit) (distance : Nat) (input : AIG.RefStream aig w)
    (assign : Assignment) (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefStream aig curr)
    : ∀ (idx : Nat) (hidx1 : idx < w) (hidx2 : curr ≤ idx),
        ⟦
          (go aig input distance curr hcurr s).aig,
          (go aig input distance curr hcurr s).stream.getRef idx hidx1,
          assign.toAIGAssignment
        ⟧
          =
        if hidx:idx < distance then
          false
        else
          ⟦aig, input.getRef (idx - distance) (by omega), assign.toAIGAssignment ⟧
        := by
  intro idx hidx1 hidx2
  generalize hgo : go aig input distance curr hcurr s = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      split at hgo
      . split
        . rw [← hgo]
          rw [go_getRef]
          rw [AIG.RefStream.getRef_push_ref_eq']
          . rw [go_denote_mem_prefix]
            . simp
            . simp [Ref.hgate]
          . rw [heq]
        . omega
      . split
        . omega
        . rw [← hgo]
          rw [go_getRef]
          rw [AIG.RefStream.getRef_push_ref_eq']
          . rw [go_denote_mem_prefix]
            . simp [heq]
            . simp [Ref.hgate]
          . rw [heq]
    | inr =>
      split at hgo
      . split
        . next hidx =>
          rw [← hgo]
          rw [go_eq_eval_getLsb]
          . simp [hidx]
          . omega
        . next hidx =>
          rw [← hgo]
          rw [go_eq_eval_getLsb]
          . simp only [hidx, ↓reduceDite, RefStream.getRef_cast, Ref_cast']
            rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
          . omega
      . split
        . omega
        . next hidx =>
          rw [← hgo]
          rw [go_eq_eval_getLsb]
          . simp [hidx]
          . omega
  . omega
termination_by w - curr

end blastShiftLeft
@[simp]
theorem blastShiftLeft_eq_eval_getLsb (aig : AIG BVBit) (target : ShiftTarget aig w)
    (assign : Assignment)
    : ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (blastShiftLeft aig target).aig,
          (blastShiftLeft aig target).stream.getRef idx hidx,
          assign.toAIGAssignment
        ⟧
          =
        if hidx:idx < target.distance then
          false
        else
          ⟦aig, target.stream.getRef (idx - target.distance) (by omega), assign.toAIGAssignment ⟧
        := by
  intros
  unfold blastShiftLeft
  apply blastShiftLeft.go_eq_eval_getLsb
  omega

end bitblast
end BVExpr
