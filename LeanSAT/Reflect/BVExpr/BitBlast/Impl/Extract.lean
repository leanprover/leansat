import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.AIG

namespace BVExpr
namespace bitblast

variable [BEq α] [Hashable α] [DecidableEq α]

structure ExtractTarget (aig : AIG α) (newWidth : Nat) where
  {w : Nat}
  stream : AIG.RefStream aig w
  hi : Nat
  lo : Nat
  hnew : newWidth = hi - lo + 1

def blastExtract (aig : AIG α) (target : ExtractTarget aig newWidth)
    : AIG.RefStreamEntry α newWidth :=
  let ⟨input, hi, lo, hnew⟩ := target
  let res := aig.mkConstCached false
  let aig := res.aig
  let falseRef := res.ref
  let input := input.cast <| by
    apply AIG.LawfulOperator.le_size (f := AIG.mkConstCached)
  if h:lo ≤ hi then
    ⟨aig, go input lo 0 (by omega) falseRef .empty⟩
  else
    have : 1 = newWidth  := by omega
    let base := AIG.RefStream.empty
    let base := base.pushRef (input.getRefD lo falseRef)
    ⟨aig, this ▸ base⟩
where
  go {aig : AIG α} {w : Nat} (input : AIG.RefStream aig w) (lo : Nat) (curr : Nat) (hcurr : curr ≤ newWidth)
      (falseRef : AIG.Ref aig) (s : AIG.RefStream aig curr)
    : AIG.RefStream aig newWidth :=
  if h : curr < newWidth then
    let nextRef := input.getRefD (lo + curr) falseRef
    let s := s.pushRef nextRef
    go input lo (curr + 1) (by omega) falseRef s
  else
    have : curr = newWidth := by omega
    this ▸ s
termination_by newWidth - curr

instance : AIG.LawfulStreamOperator α ExtractTarget blastExtract where
  le_size := by
    intros
    unfold blastExtract
    dsimp
    split
    all_goals
      simp only
      apply AIG.LawfulOperator.le_size (f := AIG.mkConstCached)
  decl_eq := by
    intros
    unfold blastExtract
    dsimp
    split
    all_goals
      simp only
      rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]

end bitblast
end BVExpr
