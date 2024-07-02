/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Extract

open AIG

namespace BVExpr
namespace bitblast

variable [BEq α] [Hashable α] [DecidableEq α]

namespace blastExtract

theorem go_getRef_aux (aig : AIG α) (input : RefStream aig w) (lo : Nat) (curr : Nat)
    (hcurr : curr ≤ newWidth) (falseRef : Ref aig) (s : RefStream aig curr)
    : ∀ (idx : Nat) (hidx1 : idx < curr),
        (go input lo curr hcurr falseRef s).getRef idx (by omega)
          =
        s.getRef idx hidx1 := by
  intro idx hidx
  generalize hgo : go input lo curr hcurr falseRef s = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    rw [← hgo]
    rw [go_getRef_aux]
    rw [AIG.RefStream.getRef_push_ref_lt]
  . dsimp at hgo
    rw [← hgo]
    simp only [RefStream.getRef, Ref.mk.injEq]
    have : curr = newWidth := by omega
    subst this
    simp
termination_by newWidth - curr

theorem go_getRef (aig : AIG α) (input : RefStream aig w) (lo : Nat) (curr : Nat)
    (hcurr : curr ≤ newWidth) (falseRef : Ref aig) (s : RefStream aig curr)
    : ∀ (idx : Nat) (hidx1 : idx < newWidth),
        curr ≤ idx
          →
        (go input lo curr hcurr falseRef s).getRef idx hidx1
          =
        input.getRefD (lo + idx) falseRef
    := by
  intro idx hidx1 hidx2
  generalize hgo : go input lo curr hcurr falseRef s = res
  unfold go at hgo
  dsimp at hgo
  split at hgo
  . rw [← hgo]
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      rw [go_getRef_aux]
      rw [AIG.RefStream.getRef_push_ref_eq']
      . simp [heq]
      . simp [heq]
    | inr heq =>
      rw [go_getRef]
      omega
  . omega
termination_by newWidth - curr

end blastExtract

@[simp]
theorem blastExtract_eq_eval_getLsb (aig : AIG α) (target : ExtractTarget aig newWidth)
    (assign : α → Bool)
  : ∀ (idx : Nat) (hidx : idx < newWidth),
      ⟦
        (blastExtract aig target).aig,
        (blastExtract aig target).stream.getRef idx hidx,
        assign
      ⟧
        =
      if h:(target.lo + idx) < target.w then
        ⟦
          aig,
          target.stream.getRef (target.lo + idx) h,
          assign
        ⟧
      else
        false
    := by
  intro idx hidx
  generalize hextract : blastExtract aig target = res
  rcases target with ⟨input, hi, lo, hnew⟩
  dsimp
  unfold blastExtract at hextract
  dsimp at hextract
  split at hextract
  . rw [← hextract]
    rw [blastExtract.go_getRef]
    . dsimp
      split
      . rw [RefStream.getRef_in_bound]
        rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
        . congr 1
        . assumption
      . rw [RefStream.getRef_out_bound]
        . simp
        . omega
    . omega
  . have : idx = 0 := by omega
    simp only [this]
    have : 1 = newWidth := by omega
    subst this
    rw [← hextract]
    split
    . rw [RefStream.getRef_in_bound]
      dsimp
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      . congr 2
      . omega
    . rw [RefStream.getRef_out_bound]
      . simp
      . omega


end bitblast
end BVExpr
