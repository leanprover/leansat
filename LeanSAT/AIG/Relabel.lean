/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.AIG.Basic
import LeanSAT.AIG.Lemmas

variable {α : Type} [Hashable α] [DecidableEq α]
variable {β : Type} [Hashable β] [DecidableEq β]

namespace Decl

def relabel (f : α → β) (decl : Decl α) : Decl β :=
  match decl with
  | .const b => .const b
  | .atom a => .atom (f a)
  | .gate lhs rhs linv rinv => .gate lhs rhs linv rinv

instance : Functor Decl where
  map := relabel

theorem relabel_id_map (decl : Decl α) : relabel id decl = decl := by
  simp only [relabel, id_eq]
  cases decl <;> rfl

theorem relabel_comp (decl : Decl α) (g : α → β) (h : β → γ) :
    relabel (h ∘ g) decl = relabel h (relabel g decl) := by
  cases decl <;> rfl

instance : LawfulFunctor Decl where
  map_const := by
    simp [Functor.mapConst, Functor.map]
  id_map := by
    intro α x
    simp [Functor.map, relabel_id_map]
  comp_map := by
    intro α β γ g h x
    simp only [Functor.map, relabel_comp]

theorem relabel_const {decls : Array (Decl α)} {f : α → β} {hidx : idx < decls.size}
    (h : relabel f decls[idx] = .const b)
    : decls[idx] = (.const b) := by
  unfold relabel at h
  split at h <;> simp_all

theorem relabel_atom {decls : Array (Decl α)} {f : α → β} {hidx : idx < decls.size}
    (h : relabel f decls[idx] = .atom a)
    : ∃ x, decls[idx] = .atom x ∧ a = f x := by
  unfold relabel at h
  split at h
  . contradiction
  . next x heq =>
    injection h with h
    exists x
    simp [heq, h]
  . contradiction

theorem relabel_gate {decls : Array (Decl α)} {f : α → β} {hidx : idx < decls.size}
    (h : relabel f decls[idx] = .gate lhs rhs linv rinv)
    : decls[idx] = (.gate lhs rhs linv rinv : Decl α) := by
  unfold relabel at h
  split at h <;> simp_all

end Decl

namespace AIG

def relabel (f : α → β) (aig : AIG α) : AIG β :=
  let decls := aig.decls.map (Decl.relabel f)
  let cache := Cache.empty decls
  {
    decls,
    cache,
    inv := by
      intro idx lhs rhs linv rinv hbound hgate
      simp [decls] at hgate
      have := Decl.relabel_gate hgate
      apply aig.inv
      assumption
  }

@[simp]
theorem relabel_size_eq_size {aig : AIG α} {f : α → β}
    : (aig.relabel f).decls.size = aig.decls.size := by
  simp [relabel]

theorem relabel_const {aig : AIG α} {f : α → β} {hidx : idx < (relabel f aig).decls.size}
    (h : (relabel f aig).decls[idx]'hidx = .const b)
    : aig.decls[idx]'(by rw [← relabel_size_eq_size (f := f)]; omega) = .const b := by
  apply Decl.relabel_const
  simpa [relabel] using h


theorem relabel_atom {aig : AIG α} {f : α → β} {hidx : idx < (relabel f aig).decls.size}
    (h : (relabel f aig).decls[idx]'hidx = .atom a)
    : ∃ x, aig.decls[idx]'(by rw [← relabel_size_eq_size (f := f)]; omega) = .atom x ∧ a = f x := by
  apply Decl.relabel_atom
  simpa [relabel] using h

theorem relabel_gate {aig : AIG α} {f : α → β} {hidx : idx < (relabel f aig).decls.size}
    (h : (relabel f aig).decls[idx]'hidx = .gate lhs rhs linv rinv)
    : aig.decls[idx]'(by rw [← relabel_size_eq_size (f := f)]; omega) = .gate lhs rhs linv rinv := by
  apply Decl.relabel_gate
  simpa [relabel] using h

@[simp]
theorem denote_relabel (aig : AIG α) (f : α → β) (start : Nat) {hidx}
    (assign : β → Bool)
    : ⟦aig.relabel f, ⟨start, hidx⟩, assign⟧
        =
      ⟦aig, ⟨start, by rw [← relabel_size_eq_size (f := f)]; omega⟩, (assign ∘ f)⟧ := by
  apply denote_idx_trichotomy
  . intro b heq1
    have heq2 := relabel_const heq1
    rw [denote_idx_const heq1]
    rw [denote_idx_const heq2]
  . intro a heq1
    rw [denote_idx_atom heq1]
    rcases relabel_atom heq1 with ⟨x, ⟨hlx, hrx⟩⟩
    rw [hrx] at heq1
    rw [denote_idx_atom hlx]
    simp [hrx]
  . intro lhs rhs linv rinv heq1
    have heq2 := relabel_gate heq1
    rw [denote_idx_gate heq1]
    rw [denote_idx_gate heq2]
    have := aig.inv start lhs rhs linv rinv (by rw [← relabel_size_eq_size (f := f)]; omega) heq2
    rw [denote_relabel aig f lhs assign]
    rw [denote_relabel aig f rhs assign]

theorem unsat_relabel {aig : AIG α} (f : α → β) {hidx}
    : aig.unsatAt idx hidx → (aig.relabel f).unsatAt idx (by simp[hidx]) := by
  intro h assign
  specialize h (assign ∘ f)
  simp [h]

theorem relabel_unsat_iff [Nonempty α] {aig : AIG α} {f : α → β} {hidx1} {hidx2}
    (hinj : ∀ x y, x ∈ aig → y ∈ aig → f x = f y → x = y)
    : (aig.relabel f).unsatAt idx hidx1 ↔ aig.unsatAt idx hidx2 := by
  constructor
  . intro h assign
    let g : β → α := fun b =>
      have em := Classical.propDecidable
      if h:∃ a, a ∈ aig ∧ f a = b then h.choose else Classical.choice inferInstance
    have h' := unsat_relabel g h
    specialize h' assign
    simp only [denote_relabel] at h'
    rw [← h']
    apply denote_congr
    . intro a hmem
      simp [g]
      split
      . next h =>
        rcases Exists.choose_spec h with ⟨_, heq⟩
        specialize hinj _ _ (by assumption) (by assumption) heq
        simp [hinj]
      . next h =>
        simp only [not_exists, not_and] at h
        specialize h a hmem
        contradiction
  . apply unsat_relabel

namespace Entrypoint

def relabel (f : α → β) (entry : Entrypoint α) : Entrypoint β :=
  { entry with
      aig := entry.aig.relabel f
      ref.hgate := by simp [entry.ref.hgate]
  }

@[simp]
theorem relabel_size_eq {entry : Entrypoint α} {f : α → β} :
    (entry.relabel f).aig.decls.size = entry.aig.decls.size := by
  simp [relabel]

theorem relabel_unsat_iff [Nonempty α] {entry : Entrypoint α} {f : α → β}
    (hinj : ∀ x y, x ∈ entry.aig → y ∈ entry.aig → f x = f y → x = y)
    : (entry.relabel f).unsat ↔ entry.unsat := by
  simp [relabel, unsat]
  rw [AIG.relabel_unsat_iff]
  assumption

end Entrypoint
end AIG
