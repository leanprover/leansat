import LeanSAT.AIG.CachedGatesLemmas

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

end AIG
