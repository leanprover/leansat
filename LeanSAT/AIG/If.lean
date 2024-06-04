import LeanSAT.AIG.CachedGatesLemmas
import LeanSAT.AIG.RefStreamOperator

namespace AIG

variable {α : Type} [BEq α] [Hashable α] [DecidableEq α]

open AIG

def mkIfCached (aig : AIG α) (input : TernaryInput aig) : Entrypoint α :=
  -- if d then l else r = ((d && l) || (!d && r))
  let res := aig.mkAndCached ⟨input.discr, input.lhs⟩
  let aig := res.aig
  let lhsRef := res.ref
  let input := input.cast <| by apply AIG.LawfulOperator.le_size (f := mkAndCached)
  let res := aig.mkNotCached input.discr
  let aig := res.aig
  let notDiscr := res.ref
  let input := input.cast <| by apply AIG.LawfulOperator.le_size (f := mkNotCached)
  let res := aig.mkAndCached ⟨notDiscr, input.rhs⟩
  let aig := res.aig
  let rhsRef := res.ref
  let lhsRef := lhsRef.cast <| by
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := mkAndCached)
    apply AIG.LawfulOperator.le_size (f := mkNotCached)
  aig.mkOrCached ⟨lhsRef, rhsRef⟩

instance : LawfulOperator α TernaryInput mkIfCached where
  le_size := by
    intros
    unfold mkIfCached
    dsimp
    apply LawfulOperator.le_size_of_le_aig_size (f := mkOrCached)
    apply LawfulOperator.le_size_of_le_aig_size (f := mkAndCached)
    apply LawfulOperator.le_size_of_le_aig_size (f := mkNotCached)
    apply LawfulOperator.le_size (f := mkAndCached)
  decl_eq := by
    intros
    unfold mkIfCached
    dsimp
    rw [LawfulOperator.decl_eq (f := mkOrCached)]
    rw [LawfulOperator.decl_eq (f := mkAndCached)]
    rw [LawfulOperator.decl_eq (f := mkNotCached)]
    rw [LawfulOperator.decl_eq (f := mkAndCached)]
    . apply LawfulOperator.lt_size_of_lt_aig_size (f := mkAndCached)
      assumption
    . apply LawfulOperator.lt_size_of_lt_aig_size (f := mkNotCached)
      apply LawfulOperator.lt_size_of_lt_aig_size (f := mkAndCached)
      assumption
    . apply LawfulOperator.lt_size_of_lt_aig_size (f := mkAndCached)
      apply LawfulOperator.lt_size_of_lt_aig_size (f := mkNotCached)
      apply LawfulOperator.lt_size_of_lt_aig_size (f := mkAndCached)
      assumption

theorem if_as_bool (d l r : Bool) : (if d then l else r) = ((d && l) || (!d && r))  := by
  revert d l r
  decide

@[simp]
theorem denote_mkIfCached {aig : AIG α} {input : TernaryInput aig} :
    ⟦aig.mkIfCached input, assign⟧
      =
    if ⟦aig, input.discr, assign⟧ then ⟦aig, input.lhs, assign⟧ else ⟦aig, input.rhs, assign⟧ := by
  rw [if_as_bool]
  unfold mkIfCached
  simp only [TernaryInput.cast, Ref_cast', id_eq, Int.reduceNeg, denote_mkOrCached,
    denote_projected_entry, denote_mkAndCached, denote_mkNotCached]
  congr 2
  . rw [LawfulOperator.denote_mem_prefix]
    rw [LawfulOperator.denote_mem_prefix]
    . simp
    . simp [Ref.hgate]
  . rw [LawfulOperator.denote_mem_prefix]
  . rw [LawfulOperator.denote_mem_prefix]
    rw [LawfulOperator.denote_mem_prefix]

namespace RefStream

structure IfInput (aig : AIG α) (w : Nat) where
  discr : Ref aig
  lhs : RefStream aig w
  rhs : RefStream aig w

def ite (aig : AIG α) (input : IfInput aig w) : RefStreamEntry α w :=
  let ⟨discr, lhs, rhs⟩ := input
  go aig 0 (by omega) discr lhs rhs .empty
where
  go {w : Nat} (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (discr : Ref aig) (lhs rhs : RefStream aig w)
      (s : RefStream aig curr) : RefStreamEntry α w :=
    if hcurr:curr < w then
      let input := ⟨discr, lhs.getRef curr hcurr, rhs.getRef curr hcurr⟩
      let res := mkIfCached aig input
      let aig := res.aig
      let ref := res.ref
      have := by
        apply LawfulOperator.le_size (f := mkIfCached)
      let discr := discr.cast this
      let lhs := lhs.cast this
      let rhs := rhs.cast this
      let s := s.cast this
      let s := s.pushRef ref
      go aig (curr + 1) (by omega) discr lhs rhs s
    else
      have : curr = w := by omega
      ⟨aig, this ▸ s⟩

namespace ite

theorem go_le_size (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (discr : Ref aig)
      (lhs rhs : RefStream aig w) (s : RefStream aig curr)
    : aig.decls.size ≤ (go aig curr hcurr discr lhs rhs s).aig.decls.size := by
  unfold go
  split
  . dsimp
    refine Nat.le_trans ?_ (by apply go_le_size)
    apply LawfulOperator.le_size (f := mkIfCached)
  . simp

theorem go_decl_eq (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (discr : Ref aig)
      (lhs rhs : RefStream aig w) (s : RefStream aig curr)
    : ∀ (idx : Nat) (h1) (h2),
       (go aig curr hcurr discr lhs rhs s).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig curr hcurr discr lhs rhs s = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    rw [← hgo]
    intro idx h1 h2
    rw [go_decl_eq]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkIfCached)]
    apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkIfCached)
    assumption
  . simp [← hgo]

end ite

instance : LawfulStreamOperator α IfInput ite where
  le_size := by
    intros
    unfold ite
    apply ite.go_le_size
  decl_eq := by
    intros
    unfold ite
    rw [ite.go_decl_eq]

namespace ite

theorem go_getRef_aux {w : Nat} (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (discr : Ref aig)
      (lhs rhs : RefStream aig w) (s : RefStream aig curr)
    : ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig curr hcurr discr lhs rhs s).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig curr hcurr discr lhs rhs s = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    rw [← hgo]
    intros
    rw [go_getRef_aux]
    rw [AIG.RefStream.getRef_push_ref_lt]
    . simp only [Ref.cast, Ref.mk.injEq]
      rw [AIG.RefStream.getRef_cast]
      . simp
      . assumption
    . apply go_le_size
  . dsimp at hgo
    rw [← hgo]
    simp only [Nat.le_refl, getRef, Ref_cast', Ref.mk.injEq, true_implies]
    congr
    . omega
    . simp

theorem go_getRef {w : Nat} (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (discr : Ref aig)
      (lhs rhs : RefStream aig w) (s : RefStream aig curr)
    : ∀ (idx : Nat) (hidx : idx < curr),
        (go aig curr hcurr discr lhs rhs s).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast (by apply go_le_size) := by
  intro idx hidx
  apply go_getRef_aux

theorem go_denote_mem_prefix {w : Nat} (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (discr : Ref aig)
      (lhs rhs : RefStream aig w) (s : RefStream aig curr) (start : Nat) (hstart)
  : ⟦
      (go aig curr hcurr discr lhs rhs s).aig,
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

theorem denote_go {w : Nat} (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (discr : Ref aig)
      (lhs rhs : RefStream aig w) (s : RefStream aig curr)
    : ∀ (idx : Nat) (hidx1 : idx < w),
        curr ≤ idx
          →
        ⟦
          (go aig curr hcurr discr lhs rhs s).aig,
          (go aig curr hcurr discr lhs rhs s).stream.getRef idx hidx1,
          assign
        ⟧
          =
        if ⟦aig, discr, assign⟧ then
          ⟦aig, lhs.getRef idx hidx1, assign⟧
        else
          ⟦aig, rhs.getRef idx hidx1, assign⟧ := by
  intro idx hidx1 hidx2
  generalize hgo : go aig curr hcurr discr lhs rhs s = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      subst heq
      rw [← hgo]
      rw [go_getRef]
      rw [AIG.RefStream.getRef_push_ref_eq']
      . rw [go_denote_mem_prefix]
        . simp
        . simp [Ref.hgate]
      . omega
    | inr heq =>
      rw [← hgo]
      rw [denote_go]
      . rw [LawfulOperator.denote_mem_prefix (f := mkIfCached)]
        rw [LawfulOperator.denote_mem_prefix (f := mkIfCached)]
        rw [LawfulOperator.denote_mem_prefix (f := mkIfCached)]
        . simp
        . simp [Ref.hgate]
        . simp [Ref.hgate]
        . simp [Ref.hgate]
      . omega
  . omega

end ite

@[simp]
theorem denote_ite {aig : AIG α} {input : IfInput aig w}
  : ∀ (idx : Nat) (hidx : idx < w),
      ⟦(ite aig input).aig, (ite aig input).stream.getRef idx hidx, assign⟧
        =
      if ⟦aig, input.discr, assign⟧ then
        ⟦aig, input.lhs.getRef idx hidx, assign⟧
      else
        ⟦aig, input.rhs.getRef idx hidx, assign⟧ := by
  intro idx hidx
  unfold ite
  dsimp
  rw [ite.denote_go]
  omega


end RefStream

end AIG
