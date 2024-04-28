import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.AIG

namespace BVExpr
namespace bitblast

structure FullAdderInput (aig : AIG BVBit) where
  lhs : AIG.Ref aig
  rhs : AIG.Ref aig
  cin : AIG.Ref aig

def mkFullAdderOut (aig : AIG BVBit) (input : FullAdderInput aig) : AIG.Entrypoint BVBit :=
  -- let subExpr = XOR lhs rhs
  -- out = XOR subExpr cin
  -- subExpr is shared in `mkFullAdderOut` and `mkFullAdderCarry`
  -- Due to automated subterm sharing in the AIG we don't have to make this explicitly sure
  let ⟨lhs, rhs, cin⟩ := input
  let res := aig.mkXorCached ⟨lhs, rhs⟩
  let aig := res.aig
  let subExprRef := res.ref
  let cin := cin.cast <| by
    apply AIG.LawfulOperator.le_size (f := AIG.mkXorCached)
  aig.mkXorCached ⟨subExprRef, cin⟩

instance : AIG.LawfulOperator BVBit FullAdderInput mkFullAdderOut where
  le_size := by
    intros
    unfold mkFullAdderOut
    dsimp
    apply AIG.LawfulOperator.le_size_of_le_aig_size
    apply AIG.LawfulOperator.le_size
  decl_eq := by
    intros
    unfold mkFullAdderOut
    dsimp
    rw [AIG.LawfulOperator.decl_eq]
    rw [AIG.LawfulOperator.decl_eq]
    apply AIG.LawfulOperator.lt_size_of_lt_aig_size
    assumption

def mkFullAdderCarry (aig : AIG BVBit) (input : FullAdderInput aig) : AIG.Entrypoint BVBit :=
  -- let subExpr = XOR lhs rhs
  -- cout = OR (AND subExpr cin) (AND lhs rhs)
  -- subExpr is shared in `mkFullAdderOut` and `mkFullAdderCarry`
  -- Due to automated subterm sharing in the AIG we don't have to make this explicitly sure
  let ⟨lhs, rhs, cin⟩ := input
  let res := aig.mkXorCached ⟨lhs, rhs⟩
  let aig := res.aig
  let subExprRef := res.ref
  have hsub := by
    apply AIG.LawfulOperator.le_size (f := AIG.mkXorCached)
  let cin := cin.cast hsub
  let res := aig.mkAndCached ⟨subExprRef, cin⟩
  let aig := res.aig
  let lorRef := res.ref
  have hlor := by
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkAndCached)
    assumption
  let lhs := lhs.cast hlor
  let rhs := rhs.cast hlor
  let res := aig.mkAndCached ⟨lhs, rhs⟩
  let aig := res.aig
  let rorRef := res.ref
  have hror := by
    apply AIG.LawfulOperator.le_size (f := AIG.mkAndCached)
  let lorRef := lorRef.cast hror
  aig.mkOrCached ⟨lorRef, rorRef⟩

instance : AIG.LawfulOperator BVBit FullAdderInput mkFullAdderCarry where
  le_size := by
    intros
    unfold mkFullAdderCarry
    dsimp
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkOrCached)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkAndCached)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkAndCached)
    apply AIG.LawfulOperator.le_size (f := AIG.mkXorCached)

  decl_eq := by
    intros
    unfold mkFullAdderCarry
    dsimp
    rw [AIG.LawfulOperator.decl_eq]
    rw [AIG.LawfulOperator.decl_eq]
    rw [AIG.LawfulOperator.decl_eq]
    rw [AIG.LawfulOperator.decl_eq]
    . apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkXorCached)
      assumption
    . apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkAndCached)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkXorCached)
      assumption
    . apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkAndCached)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkAndCached)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkXorCached)
      assumption

def blastAdd (aig : AIG BVBit) (input : AIG.BinaryRefStream aig w) : AIG.RefStreamEntry BVBit w :=
  let res := aig.mkConstCached false
  let aig := res.aig
  let cin := res.ref
  let input := input.cast <| by
    apply AIG.LawfulOperator.le_size (f := AIG.mkConstCached)
  let ⟨lhs, rhs⟩ := input
  go aig 0 (by omega) cin .empty lhs rhs
where
  go {w : Nat} (aig : AIG BVBit) (curr : Nat) (hcurr : curr ≤ w) (cin : AIG.Ref aig)
      (s : AIG.RefStream aig curr) (lhs rhs : AIG.RefStream aig w)
      : AIG.RefStreamEntry BVBit w :=
    if hidx:curr < w then
      let lin := lhs.getRef curr hidx
      let rin := rhs.getRef curr hidx
      let res := mkFullAdderOut aig ⟨lin, rin, cin⟩
      let aig := res.aig
      let outRef := res.ref
      have haig1 := by
        apply AIG.LawfulOperator.le_size (f := mkFullAdderOut)
      let lin := lin.cast haig1
      let rin := rin.cast haig1
      let cin := cin.cast haig1
      let res := mkFullAdderCarry aig ⟨lin, rin, cin⟩
      let aig := res.aig
      let carryRef := res.ref
      have haig2 := by
        apply AIG.LawfulOperator.le_size (f := mkFullAdderCarry)
      have hchained := by
        -- TODO: This proof isn't nice
        simp (config := {zetaDelta := true}) only at haig1 haig2 |-
        omega
      let s := s.cast hchained
      let outRef := outRef.cast haig2
      let lhs := lhs.cast hchained
      let rhs := rhs.cast hchained
      let s := s.pushRef outRef
      go aig (curr + 1) (by omega) carryRef s lhs rhs
    else
      have hcurr : curr = w := by omega
      ⟨aig, hcurr ▸ s⟩
  termination_by w - curr

instance : AIG.LawfulStreamOperator BVBit AIG.BinaryRefStream blastAdd where
  le_size := sorry
  decl_eq := sorry

end bitblast
end BVExpr
