import LeanSAT.AIG.CachedGatesLemmas
import LeanSAT.AIG.RefStream

namespace BVPred

variable [BEq α] [Hashable α] [DecidableEq α]

structure GetLsbTarget (aig : AIG α) where
  {w : Nat}
  stream : AIG.RefStream aig w
  idx : Nat

def blastGetLsb (aig : AIG α) (target : GetLsbTarget aig) : AIG.Entrypoint α :=
  if h:target.idx < target.w then
    ⟨aig, target.stream.getRef target.idx h⟩
  else
    AIG.mkConstCached aig false

instance : AIG.LawfulOperator α GetLsbTarget blastGetLsb where
  le_size := by
    intros
    unfold blastGetLsb
    split
    . simp
    . apply AIG.LawfulOperator.le_size (f := AIG.mkConstCached)
  decl_eq := by
    intros
    unfold blastGetLsb
    split
    . simp
    . rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]

end BVPred
