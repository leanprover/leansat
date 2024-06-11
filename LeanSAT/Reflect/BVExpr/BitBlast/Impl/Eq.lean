import LeanSAT.AIG

namespace BVPred

variable [BEq α] [Hashable α] [DecidableEq α]

def mkEq (aig : AIG α) (pair : AIG.BinaryRefStream aig w) : AIG.Entrypoint α :=
  let res := AIG.RefStream.zip aig ⟨pair, AIG.mkBEqCached⟩
  let aig := res.aig
  let bits := res.stream
  AIG.RefStream.fold aig (.mkAnd bits)

instance {w : Nat} : AIG.LawfulOperator α (AIG.BinaryRefStream · w) mkEq where
  le_size := by
    intros
    unfold mkEq
    dsimp
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.RefStream.fold)
    apply AIG.LawfulStreamOperator.le_size (f := AIG.RefStream.zip)
  decl_eq := by
    intros
    unfold mkEq
    dsimp
    rw [AIG.LawfulOperator.decl_eq (f := AIG.RefStream.fold)]
    rw [AIG.LawfulStreamOperator.decl_eq (f := AIG.RefStream.zip)]
    apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := AIG.RefStream.zip)
    assumption

end BVPred
