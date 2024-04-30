/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import Std.Data.Array.Lemmas

-- Various helper theorems/definitions copied from mathlib
namespace Misc -- Adding this namespace to avoid naming conflicts with the actual mathlib theorems

open List

theorem Subtype.ext {p : α → Prop} : ∀ {a1 a2 : { x // p x }}, (a1 : α) = (a2 : α) → a1 = a2
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem Subtype.ext_iff {p : α → Prop} {a1 a2 : { x // p x }} : a1 = a2 ↔ (a1 : α) = (a2 : α) :=
  ⟨congrArg _, Subtype.ext⟩

theorem Decidable.not_forall {p : α → Prop} [Decidable (∃ x, ¬p x)] [∀ x, Decidable (p x)] :
  (¬∀ x, p x) ↔ ∃ x, ¬p x :=
  ⟨Decidable.not_imp_symm fun nx x => Decidable.not_imp_symm (fun h => ⟨x, h⟩) nx, not_forall_of_exists_not⟩

@[simp]
theorem not_forall {p : α → Prop} : (¬∀ x, p x) ↔ ∃ x, ¬p x := by
  have em := Classical.propDecidable
  apply Decidable.not_forall

class IsEmpty (α : Sort _) : Prop where
  protected false : α → False

@[elab_as_elim]
def isEmptyElim [IsEmpty α] {p : α → Sort _} (a : α) : p a :=
  (IsEmpty.false a).elim

@[simp]
theorem IsEmpty.forall_iff [IsEmpty α] {p : α → Prop} : (∀ a, p a) ↔ True :=
  iff_true_intro isEmptyElim

theorem forall_prop_of_false {p : Prop} {q : p → Prop} (hn : ¬p) : (∀ h' : p, q h') ↔ True :=
  iff_true_intro fun h => hn.elim h

@[simp] theorem dite_eq_left_iff [Decidable P] : dite P (fun _ => a) B = a ↔ ∀ h, B h = a := by
  by_cases P <;> simp [*, forall_prop_of_true, forall_prop_of_false]

@[simp] theorem dite_eq_right_iff [Decidable P] : (dite P A fun _ => b) = b ↔ ∀ h, A h = b := by
  by_cases P <;> simp [*, forall_prop_of_true, forall_prop_of_false]

@[simp]
theorem Bool.exists_bool {p : Bool → Prop} : (∃ b, p b) ↔ p false ∨ p true :=
  ⟨fun ⟨b, h⟩ => by cases b; exact Or.inl h; exact Or.inr h,
  fun h => match h with
  | .inl h => ⟨_, h⟩
  | .inr h => ⟨_, h⟩ ⟩

@[simp]
theorem Bool.decide_coe (b : Bool) {h} : @decide b h = b := by
  cases b
  · exact decide_eq_false $ λ j => by cases j
  · exact decide_eq_true $ rfl

theorem Bool.coe_decide (p : Prop) [d : Decidable p] : decide p ↔ p :=
  match d with
  | isTrue hp => ⟨λ _ => hp, λ _ => rfl⟩
  | isFalse hnp => ⟨λ h => Bool.noConfusion h, λ hp => (hnp hp).elim⟩

theorem Bool.of_decide_iff {p : Prop} [Decidable p] : decide p ↔ p := Bool.coe_decide p

theorem Bool.eq_not_iff : ∀ {a b : Bool}, a = !b ↔ a ≠ b := by
  intro a b
  cases a <;> cases b <;> decide

@[simp]
theorem Prod.mk.eta : ∀ {p : α × β}, (p.1, p.2) = p
  | (_, _) => rfl

@[simp]
theorem Prod.forall {p : α × β → Prop} : (∀ x, p x) ↔ ∀ a b, p (a, b) :=
  ⟨fun h a b => h (a, b), fun h ⟨a, b⟩ => h a b⟩

@[simp]
theorem Prod.exists {p : α × β → Prop} : (∃ x, p x) ↔ ∃ a b, p (a, b) :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

theorem Prod.lex_def (r : α → α → Prop) (s : β → β → Prop) {p q : α × β} :
    Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2 :=
  ⟨fun h ↦ by cases h <;> simp [*], fun h ↦
    match p, q, h with
    | (a, b), (c, d), Or.inl h => Prod.Lex.left _ _ h
    | (a, b), (c, d), Or.inr ⟨e, h⟩ => by subst e; exact Prod.Lex.right _ h⟩

@[simp]
theorem forall_mem_ne {a : α} {l : List α} : (∀ a' : α, a' ∈ l → ¬a = a') ↔ a ∉ l :=
  ⟨fun h m => h _ m rfl, fun h _ m e => h (e.symm ▸ m)⟩

@[simp]
theorem List.nodup_nil : @Nodup α [] :=
  Pairwise.nil

@[simp]
theorem List.nodup_cons {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  simp only [Nodup, pairwise_cons, forall_mem_ne]

theorem List.Nodup.cons (ha : a ∉ l) (hl : Nodup l) : Nodup (a :: l) :=
  nodup_cons.2 ⟨ha, hl⟩

theorem List.nodup_append {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ Nodup l₁ ∧ Nodup l₂ ∧ Disjoint l₁ l₂ :=
  by simp only [Nodup, pairwise_append, disjoint_iff_ne]

theorem List.Nodup.erase_eq_filter [BEq α] [LawfulBEq α] {l} (d : Nodup l) (a : α) : l.erase a = l.filter (· != a) := by
  induction d -- with b l m _ IH; · rfl
  . rfl
  . next b l m _ IH =>
    by_cases h : b = a
    · subst h
      rw [erase_cons_head, filter_cons_of_neg _ (by simp)]
      apply Eq.symm
      rw [filter_eq_self]
      simpa [@eq_comm α] using m
    · simp [beq_false_of_ne h, IH, h]

theorem List.Nodup.mem_erase_iff [BEq α] [LawfulBEq α] {a : α} (d : Nodup l) : a ∈ l.erase b ↔ a != b ∧ a ∈ l := by
  rw [List.Nodup.erase_eq_filter d, mem_filter, and_comm]

theorem List.Nodup.not_mem_erase [BEq α] [LawfulBEq α] {a : α} (h : Nodup l) : a ∉ l.erase a := fun H => by
  have h := ((List.Nodup.mem_erase_iff h).mp H).left
  simp only [bne_self_eq_false] at h

theorem List.Nodup.sublist : l₁ <+ l₂ → Nodup l₂ → Nodup l₁ :=
  Pairwise.sublist

theorem List.Nodup.erase [BEq α] [LawfulBEq α] (a : α) : Nodup l → Nodup (l.erase a) :=
  List.Nodup.sublist <| erase_sublist _ _

def List.Pairwise_iff.{u_1} {α : Type u_1} (R : α → α → Prop) (l : List α) : List.Pairwise R l ↔
  l = [] ∨ Exists fun {a} => Exists fun {l'} => (∀ (a' : α), a' ∈ l' → R a a') ∧
    List.Pairwise R l' ∧ l = a :: l' := by
  induction l with
  | nil => simp
  | cons hd tl _ =>
    simp only [List.pairwise_cons, List.cons.injEq, false_or]
    constructor
    . intro h
      apply Exists.intro hd
      apply Exists.intro tl
      exact ⟨h.1, h.2, rfl, rfl⟩
    . intro h
      rcases h with ⟨a, l', h1, h2, h3, h4⟩
      rw [h3, h4]
      exact ⟨h1, h2⟩

theorem List.Pairwise.imp_of_mem {R S : α → α → Prop} {l : List α}
  (H : ∀ {a b}, a ∈ l → b ∈ l → R a b → S a b) (p : List.Pairwise R l) : List.Pairwise S l := by
  induction p with
  | nil => constructor
  | @cons a l r _ ih =>
    constructor
    · intro a' a'_in_l
      have a_in_al : a ∈ a :: l := by simp
      have a'_in_al : a' ∈ a :: l := by simp [a'_in_l]
      exact H a_in_al a'_in_al (r a' a'_in_l)
    · exact ih fun {a b} m m' => H (List.mem_cons_of_mem _ m) (List.mem_cons_of_mem _ m')

theorem List.Pairwise.iff_of_mem {R S : α → α → Prop} {l : List α}
  (H : ∀ {a b}, a ∈ l → b ∈ l → (R a b ↔ S a b)) : List.Pairwise R l ↔ List.Pairwise S l :=
  ⟨Pairwise.imp_of_mem fun {_ _} m m' => (H m m').1, Pairwise.imp_of_mem fun {_ _} m m' => (H m m').2⟩

theorem List.Pairwise.iff {R S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} :
  List.Pairwise R l ↔ List.Pairwise S l := Pairwise.iff_of_mem fun _ _ => H _ _

def List.foldlRecOn {C : β → Sort _} (l : List α) (op : β → α → β) (b : β) (hb : C b)
  (hl : ∀ (b : β) (_ : C b) (a : α) (_ : a ∈ l), C (op b a)) : C (List.foldl op b l) := by
  cases l with
  | nil => exact hb
  | cons hd tl =>
    have IH : (b : β) → C b → ((b : β) → C b → (a : α) → a ∈ tl → C (op b a)) → C (List.foldl op b tl) :=
      foldlRecOn _ _
    refine' IH _ _ _
    · exact hl b hb hd (List.mem_cons_self hd tl)
    · intro y hy x hx
      exact hl y hy x (List.mem_cons_of_mem hd hx)

theorem Nat.eq_one_of_mul_eq_one_right (H : m * n = 1) : m = 1 :=
  Nat.eq_one_of_dvd_one ⟨n, H.symm⟩

theorem Nat.eq_one_of_mul_eq_one_left (H : m * n = 1) : n = 1 :=
  Nat.eq_one_of_mul_eq_one_right (by rwa [Nat.mul_comm])

theorem Nat.mul_eq_one {a b : Nat} : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  constructor
  . intro h
    exact ⟨Nat.eq_one_of_mul_eq_one_right h, Nat.eq_one_of_mul_eq_one_left h⟩
  . intro h
    rw [h.1, h.2]

theorem Nat.add_eq_zero {a b : Nat} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  . exact Nat.eq_zero_of_add_eq_zero
  . intro h
    rw [h.1, h.2]

theorem Nat.add_left_eq_self {a b : Nat} : a + b = b ↔ a = 0 := by
  constructor
  . intro h
    conv at h =>
      rhs
      rw [← Nat.zero_add b]
    exact Nat.add_right_cancel h
  . intro h
    rw [h, Nat.zero_add]

theorem Nat.gt_one_of_gt_zero_of_ne_one {n : Nat} (h0 : n > 0) (h1 : n ≠ 1) : n > 1 :=
  Nat.lt_of_le_of_ne h0 (id (Ne.symm h1))

theorem Nat.eq_zero_of_zero_dvd {a : Nat} (h : 0 ∣ a) : a = 0 := by
  rw [Nat.dvd_iff_mod_eq_zero] at h
  simp only [Nat.mod_zero] at h
  exact h

theorem Nat.zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
  ⟨eq_zero_of_zero_dvd, fun h => by
    rw [h]
    exact ⟨0, by simp⟩⟩

theorem Nat.mul_lt_mul_left (h : 0 < a) : a * b < a * c ↔ b < c := by
  constructor
  . intro h
    exact Nat.gt_of_not_le fun hle : c ≤ b =>
      have : a * c ≤ a * b := Nat.mul_le_mul_left a hle
      have : ¬ a * b < a * c := Nat.not_lt_of_le this
      absurd h this
  . intro h; apply Nat.mul_lt_mul_of_pos_left <;> assumption

theorem Nat.eq_mul_of_div_eq_right {a b c : Nat} (H1 : b ∣ a) (H2 : a / b = c) : a = b * c := by
  rw [← H2, Nat.mul_div_cancel' H1]

theorem Nat.lt_div_iff_mul_lt {n d : Nat} (hnd : d ∣ n) (a : Nat) : a < n / d ↔ d * a < n := by
  rcases d.eq_zero_or_pos with (rfl | hd0); · simp [zero_dvd_iff.mp hnd]
  rw [← mul_lt_mul_left hd0, ← Nat.eq_mul_of_div_eq_right hnd rfl]

theorem Nat.lt_of_mul_lt_mul_left (h : a * b < a * c) (a0 : 0 < a) : b < c := by
  rw [← Nat.mul_lt_mul_left a0]
  exact h

theorem Nat.div_lt_of_lt_mul {m n k : Nat} (h : m < n * k) (h0 : 0 < n) : m / n < k :=
  Nat.lt_of_mul_lt_mul_left
    (calc
      n * (m / n) ≤ m % n + n * (m / n) := Nat.le_add_left _ _
      _ = m := Nat.mod_add_div _ _
      _ < n * k := h
      )
    h0

theorem Nat.le_mul_of_pos_left (h : 0 < n) : m ≤ n * m := by
  conv =>
    lhs
    rw [← Nat.one_mul m]
  exact Nat.mul_le_mul_right _ $ Nat.succ_le_of_lt h

@[simp]
theorem mul_eq_mul_right_iff : a * c = b * c ↔ a = b ∨ c = 0 := by
  by_cases hc : c = 0
  . simp only [hc, Nat.mul_zero, or_true]
  . simp only [hc, or_false]
    have zero_lt_c : 0 < c := Nat.zero_lt_of_ne_zero hc
    constructor
    . exact Nat.eq_of_mul_eq_mul_right zero_lt_c
    . intro h
      rw [h]

@[simp]
theorem mul_eq_mul_left_iff : a * b = a * c ↔ b = c ∨ a = 0 := by
  by_cases ha : a = 0
  . simp only [ha, Nat.zero_mul, or_true]
  . simp only [ha, or_false]
    have zero_lt_a : 0 < a := Nat.zero_lt_of_ne_zero ha
    constructor
    . exact Nat.eq_of_mul_eq_mul_left zero_lt_a
    . intro h
      rw [h]

def Xor' (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)
def Even (a : Nat) := ∃ r : Nat, a = r + r
def Odd (a : Nat) := ∃ k : Nat, a = 2 * k + 1

theorem Nat.mod_add_div (m k : Nat) : m % k + k * (m / k) = m := by
  induction m, k using Nat.mod.inductionOn with rw [Nat.div_eq, Nat.mod_eq]
  | base x y h => simp only [h, ite_false, Nat.mul_zero, Nat.add_zero]
  | ind x y h IH =>
    simp only [h, and_self, ite_true]
    rw [Nat.mul_succ, ← Nat.add_assoc, IH, Nat.sub_add_cancel h.2]

theorem Nat.even_iff : Even n ↔ n % 2 = 0 :=
  ⟨fun ⟨m, hm⟩ => by simp only [hm, ← Nat.two_mul, Nat.mul_mod_right], fun h =>
    ⟨n / 2, (mod_add_div n 2).symm.trans (by simp only [h, Nat.zero_add, Nat.two_mul])⟩⟩

theorem Nat.odd_iff : Odd n ↔ n % 2 = 1 :=
  ⟨fun ⟨m, hm⟩ => by rw [hm, Nat.add_mod, Nat.mul_mod_right],
    fun h => ⟨n / 2, (mod_add_div n 2).symm.trans (by rw [h, Nat.add_comm])⟩⟩

theorem Nat.odd_succ_of_even : Even n → Odd n.succ := by
  intro ⟨r, hr⟩; exists r; simp_arith [hr]

theorem Nat.even_succ_of_odd : Odd n → Even n.succ := by
  intro ⟨r, hr⟩; exists (r+1); simp_arith [*]

theorem Nat.two_div_iff_even : 2 ∣ n ↔ Even n := by
  unfold Even
  simp only [← Nat.two_mul]
  constructor
  all_goals
    intro heven
    rcases heven with ⟨i, hi⟩
    exists i

theorem Nat.mod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  . simp (config := { decide := true}) only [h]
  . simp (config := { decide := true}) only [h]

theorem Nat.mul_div_cancel_left' {a b : Nat} (Hd : a ∣ b) : a * (b / a) = b := by
  rw [Nat.mul_comm, Nat.div_mul_cancel Hd]

theorem Nat.not_even_iff : ¬Even n ↔ n % 2 = 1 := by rw [even_iff, mod_two_ne_zero]

theorem Nat.odd_iff_not_even : Odd n ↔ ¬Even n := by rw [not_even_iff, odd_iff]

theorem Nat.not_odd_iff_even : ¬ Odd n ↔ Even n := by rw [odd_iff_not_even, Classical.not_not]

theorem Nat.odd_pred_of_even (h : n > 0) : Even n → Odd (n-1) := by
  intro; apply Classical.byContradiction
  intro h'
  have := Iff.mp Nat.not_odd_iff_even h'
  have : Odd (n - 1 + 1) := Nat.odd_succ_of_even this
  rw [Nat.sub_add_cancel h] at this
  have := Iff.mp Nat.odd_iff_not_even this
  contradiction

theorem Nat.even_pred_of_odd (h : n > 0) : Odd n → Even (n-1) := by
  intro; apply Classical.byContradiction
  intro h'
  have := Iff.mpr Nat.odd_iff_not_even h'
  have : Even (n - 1 + 1) := Nat.even_succ_of_odd this
  rw [Nat.sub_add_cancel h] at this
  have := Iff.mpr Nat.not_odd_iff_even this
  contradiction

instance (n : Nat) : Decidable (Even n) := decidable_of_iff (n % 2 = 0) Nat.even_iff.symm

theorem Nat.even_xor_odd (n : Nat) : Xor' (Even n) (Odd n) := by
  simp only [Xor', odd_iff_not_even, Classical.not_not, and_self, Decidable.em (Even n)]

theorem Nat.sub_mod_eq_zero_of_mod_eq {m n k : Nat} (h : m % k = n % k) : (m - n) % k = 0 := by
  rw [← Nat.mod_add_div m k, ← Nat.mod_add_div n k, ← h, Nat.sub_add_eq,
    Nat.add_sub_cancel_left, ← Nat.mul_sub_left_distrib, Nat.mul_mod_right]

theorem Array.range_size {n : Nat} : (Array.range n).size = n := by
  induction n
  . decide
  . next n ih =>
    simp only [Array.range, Nat.fold, flip, Array.size_push, Nat.succ.injEq]
    simp only [Array.range, flip] at ih
    exact ih

theorem Array.range_idx {n : Nat} {x : Nat} (h : x < n) : (Array.range n)[x]'(by rw [Array.range_size]; exact h) = x := by
  induction n
  . contradiction
  . next n ih =>
    rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ h with x_lt_n | x_eq_n
    . specialize ih x_lt_n
      simp only [Array.range, Nat.fold, flip, Array.get_push]
      simp only [Array.range, flip] at ih
      split
      . exact ih
      . next x_ge_n =>
        exfalso
        have h_range_size : (Array.range n).size = n := Array.range_size
        simp only [Array.mkEmpty_eq, Array.range, flip] at h_range_size
        simp only [Array.mkEmpty_eq, h_range_size] at x_ge_n
        exact x_ge_n x_lt_n
    . simp only [Array.range, Nat.fold, flip, Array.get_push]
      split
      . next x_lt_n =>
        exfalso
        have h_range_size : (Array.range n).size = n := Array.range_size
        simp only [Array.range, Array.mkEmpty_eq] at h_range_size
        simp only [x_eq_n, Array.mkEmpty_eq, h_range_size, Nat.lt_irrefl] at x_lt_n
      . rw [x_eq_n]

theorem Array.mem_filter {a : Array α} {p : α → Bool} :
  ∀ i : Nat, ∀ i_in_bounds : i < a.size, p (a[i]'i_in_bounds) → (a[i]'i_in_bounds) ∈ (a.filter p).data := by
  intro i i_in_bounds pai
  simp only [Array.filter]
  let motive (idx : Nat) (acc : Array α) : Prop :=
    ∀ i : Nat, ∀ i_in_bounds : i < a.size, i < idx → p (a[i]'i_in_bounds) → (a[i]'i_in_bounds) ∈ acc.data
  have h_base : motive 0 #[] := by
    intro i i_in_bounds i_lt_zero
    exact False.elim $ Nat.not_lt_zero i i_lt_zero
  let f := (fun acc x => if p x = true then Array.push acc x else acc)
  have f_def : f = (fun acc x => if p x = true then Array.push acc x else acc) := rfl
  have h_inductive (idx : Fin a.size) (acc : Array α) (ih : motive idx.1 acc) : motive (idx.1 + 1) (f acc a[idx]) := by
    intro i i_in_bounds i_lt_idx_add_one
    rw [f_def]
    simp only [getElem_fin]
    intro pai
    rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ i_lt_idx_add_one with i_lt_idx | i_eq_idx
    . have h := ih i i_in_bounds i_lt_idx pai
      split
      . simp only [Array.push_data, mem_append, mem_singleton]
        exact Or.inl h
      . exact h
    . split
      . simp only [i_eq_idx, Array.push_data, mem_append, mem_singleton, or_true]
      . next pa_idx =>
        simp only [← i_eq_idx] at pa_idx
        exact False.elim $ pa_idx pai
  exact Array.foldl_induction motive h_base h_inductive i i_in_bounds i_in_bounds pai

theorem Array.set!_preserves_size {a : Array α} {i : Nat} {x : α} : (a.set! i x).size = a.size := by
  rw [Array.set!, Array.setD]
  split
  . simp only [Array.size_set]
  . rfl

theorem Array.modify_preserves_size {a : Array α} {i : Nat} {f : α → α} : (a.modify i f).size = a.size := by
  simp only [Array.modify, Array.modifyM, Id.bind_eq, Id.pure_eq, Id.run]
  split
  . simp only [Array.size_set]
  . rfl

theorem Array.get_modify_at_idx {a : Array α} {i : Nat} (i_in_bounds : i < a.size) (f : α → α) :
  (a.modify i f)[i]'(by rw [Array.modify_preserves_size]; exact i_in_bounds) = f (a[i]) := by
  simp only [Array.modify, Array.modifyM, Id.bind_eq, Id.pure_eq, Id.run]
  split
  . simp only [getElem]
    have lhs_rw := Array.get_set a ⟨i, i_in_bounds⟩ i i_in_bounds (f (Array.get a ⟨i, i_in_bounds⟩))
    simp only [getElem] at lhs_rw
    rw [lhs_rw]
    simp only [Array.get_eq_getElem, ite_true]
  . next i_out_of_bounds =>
    exfalso
    exact i_out_of_bounds i_in_bounds

theorem Array.get_modify_unchanged {a : Array α} {i : Nat} (i_size : i < a.size) {j : Nat} (j_size : j < a.size)
  (f : α → α) (h : i ≠ j) : (a.modify i f)[j]'(by rw [Array.modify_preserves_size]; exact j_size) = a[j] := by
  simp only [Array.modify, Array.modifyM, Id.bind_eq, Id.pure_eq, Id.run]
  split
  . simp only [getElem]
    have lhs_rw := Array.get_set a ⟨i, i_size⟩ j j_size (f (Array.get a ⟨i, i_size⟩))
    simp only [getElem] at lhs_rw
    rw [lhs_rw]
    simp only [h, Array.get_eq_getElem, ite_false]
  . next i_out_of_bounds =>
    exfalso
    exact i_out_of_bounds i_size
