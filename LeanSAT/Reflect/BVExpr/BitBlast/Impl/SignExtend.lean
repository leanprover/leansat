import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.AIG
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.ZeroExtend

namespace BVExpr
namespace bitblast

def blastSignExtend (aig : AIG BVBit) (target : AIG.ExtendTarget aig newWidth)
    : AIG.RefStreamEntry BVBit newWidth :=
  let ⟨width, input⟩ := target
  if hw:width = 0 then
    blastZeroExtend aig ⟨width, input⟩
  else
    ⟨aig, go width (by omega) input newWidth 0 (by omega) .empty⟩
where
  go {aig : AIG BVBit} (w : Nat) (hw : 0 < w) (input : AIG.RefStream aig w) (newWidth : Nat)
      (curr : Nat) (hcurr : curr ≤ newWidth) (s : AIG.RefStream aig curr) : AIG.RefStream aig newWidth :=
    if hcurr1:curr < newWidth then
      if hcurr2:curr < w then
        let s := s.pushRef (input.getRef curr hcurr2)
        go w hw input newWidth (curr + 1) (by omega) s
      else
        let s := s.pushRef (input.getRef (w - 1) (by omega))
        go w hw input newWidth (curr + 1) (by omega) s
    else
      have hcurr : curr = newWidth := by omega
      hcurr ▸ s
termination_by newWidth - curr

instance : AIG.LawfulStreamOperator BVBit AIG.ExtendTarget blastSignExtend where
  le_size := by
    intros
    unfold blastSignExtend
    dsimp
    split
    . apply AIG.LawfulStreamOperator.le_size (f := blastZeroExtend)
    . simp
  decl_eq := by
    intros
    unfold blastSignExtend
    dsimp
    split
    . rw [AIG.LawfulStreamOperator.decl_eq (f := blastZeroExtend)]
    . simp

end bitblast
end BVExpr
