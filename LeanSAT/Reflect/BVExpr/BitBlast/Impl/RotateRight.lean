import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.AIG

namespace BVExpr
namespace bitblast

/-
@[simp]
theorem getLsb_rotateRight {x : BitVec w} {r i : Nat} :
    (x.rotateRight r).getLsb i =
      cond (i < w - (r % w))
      (x.getLsb ((r % w) + i))
      (decide (i < w) && x.getLsb (i - (w - (r % w))))
-/

def blastRotateRight (aig : AIG BVBit) (target : AIG.ShiftTarget aig w)
    : AIG.RefStreamEntry BVBit w :=
  let ⟨input, distance⟩ := target
  ⟨aig, go input distance 0 (by omega) .empty⟩
where
  go {aig : AIG BVBit} (input : AIG.RefStream aig w) (distance : Nat) (curr : Nat) (hcurr : curr ≤ w)
      (s : AIG.RefStream aig curr)
    : AIG.RefStream aig w :=
  if hcurr1:curr < w then
    if hcurr2:curr < w - distance % w then
      let ref := input.getRef ((distance % w) + curr) (by omega)
      let s := s.pushRef ref
      go input distance (curr + 1) (by omega) s
    else
      let ref := input.getRef (curr - (w - (distance % w))) (by omega)
      let s := s.pushRef ref
      go input distance (curr + 1) (by omega) s
  else
    have hcurr : curr = w := by omega
    hcurr ▸ s
termination_by w - curr

instance : AIG.LawfulStreamOperator BVBit AIG.ShiftTarget blastRotateRight where
  le_size := by
    intros
    unfold blastRotateRight
    dsimp
    omega
  decl_eq := by
    intros
    unfold blastRotateRight
    dsimp

end bitblast
end BVExpr
