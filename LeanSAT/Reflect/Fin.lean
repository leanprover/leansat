/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

namespace DecidableForallFin

private def r (f : Fin (n + 1) → α) : (Fin n → α) × α :=
  ⟨fun i => f i.succ, f 0⟩

private def s (f : (Fin n → α) × α) : Fin (n + 1) → α
  | ⟨0, _⟩ => f.2
  | ⟨i + 1, h⟩ => f.1 ⟨i, Nat.lt_of_succ_lt_succ h⟩

private theorem s_r : s (r f) = f := funext fun | ⟨0, _⟩ => rfl | ⟨_ + 1, _⟩ => rfl

instance decidableForallFin (n : Nat) (p : (Fin n → Bool) → Prop) [i : DecidablePred p] :
    Decidable (∀ f, p f) :=
  match n, p, i with
  | 0, p, i =>
    match h : decide (p nofun) with
    | true => .isTrue fun f => by
        have t : f = nofun := funext nofun
        subst t
        exact of_decide_eq_true h
    | false => .isFalse fun f => by
        simp only [decide_eq_false_iff_not] at h
        exact h (f _)
  | (n+1), p, i =>
    match h : @decide (∀ f : Fin n → Bool, ∀ x : Bool, p (s (f, x))) (decidableForallFin n _) with
    | true => .isTrue <| by
        simp only [decide_eq_true_eq] at h
        intro f
        specialize h (r f).1 (r f).2
        rwa [s_r] at h
    | false => .isFalse <| by
        simp only [decide_eq_false_iff_not] at h
        exact fun w => h fun f x => w (s (f, x))

end DecidableForallFin
