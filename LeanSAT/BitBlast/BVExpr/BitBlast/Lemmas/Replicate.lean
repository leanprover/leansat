/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.BitBlast.Lemmas.Basic
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Replicate

open AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastReplicate

private theorem aux1 {a b c : Nat} (h : b < a * c) : 0 < a := by
  by_cases a = 0
  · simp_all
  · omega

private theorem aux2 {a b c : Nat} (hidx1 : b < c * a) : b % c < c := by
  apply Nat.mod_lt
  apply aux1
  assumption

private theorem aux3 {a b c : Nat} (hidx : a < b * c) (h : c < n) : a < b * n := by
  apply Nat.lt_trans
  · exact hidx
  · apply (Nat.mul_lt_mul_left _).mpr h
    apply aux1
    assumption

private theorem aux4 {a b c : Nat} (hidx : a < b * c) (h : c ≤ n) : a < b * n := by
  cases Nat.lt_or_eq_of_le h with
  | inl h => apply aux3 <;> assumption
  | inr h => simp_all

theorem go_get_aux (aig : AIG α) (n : Nat) (curr : Nat) (hcurr : curr ≤ n)
    (input : AIG.RefStream aig w) (s : AIG.RefStream aig (w * curr))
    : ∀ (idx : Nat) (hidx : idx < w * curr),
        (go n curr hcurr input s).get idx (aux4 hidx hcurr)
          =
        s.get idx hidx := by
  intro idx hidx
  unfold go
  split
  . dsimp
    rw [go_get_aux]
    rw [AIG.RefStream.get_append]
    simp only [hidx, ↓reduceDIte]
    omega
  . dsimp
    simp only [RefStream.get, Ref.mk.injEq]
    have : curr = n := by omega
    subst this
    simp
termination_by n - curr

theorem go_get (aig : AIG α) (n : Nat) (curr : Nat) (hcurr : curr ≤ n)
    (input : AIG.RefStream aig w) (s : AIG.RefStream aig (w * curr))
  : ∀ (idx : Nat) (hidx1 : idx < w * n),
      w * curr ≤ idx
        →
      (go n curr hcurr input s).get idx hidx1
        =
      input.get (idx % w) (aux2 hidx1) := by
  intro idx hidx1 hidx2
  unfold go
  dsimp
  split
  . cases Nat.lt_or_ge idx (w * (curr + 1)) with
    | inl h =>
      rw [go_get_aux]
      rw [AIG.RefStream.get_append]
      . have : ¬ (idx < w * curr) := by omega
        simp only [this, ↓reduceDIte]
        congr 1
        rw [← Nat.sub_mul_mod (k := curr)]
        . rw [Nat.mod_eq_of_lt]
          apply Nat.sub_lt_left_of_lt_add <;> assumption
        . assumption
      . simpa using h
    | inr h =>
      rw [go_get]
      assumption
  . have : curr = n := by omega
    rw [this] at hidx2
    omega
termination_by n - curr

end blastReplicate

@[simp]
theorem blastReplicate_eq_eval_getLsb (aig : AIG α) (target : ReplicateTarget aig newWidth)
    (assign : α → Bool)
  : ∀ (idx : Nat) (hidx : idx < newWidth),
      ⟦
        (blastReplicate aig target).aig,
        (blastReplicate aig target).stream.get idx hidx,
        assign
      ⟧
        =
      ⟦
        aig,
        target.inner.get (idx % target.w) (blastReplicate.aux2 (target.h ▸ hidx)),
        assign
      ⟧ := by
  intro idx hidx
  rcases target with ⟨n, input, h⟩
  unfold blastReplicate
  dsimp
  subst h
  rw [blastReplicate.go_get]
  omega
