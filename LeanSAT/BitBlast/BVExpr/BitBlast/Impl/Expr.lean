/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Var
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Const
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Not
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.ShiftLeft
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.ShiftRight
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Add
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.ZeroExtend
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Append
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Extract
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.RotateLeft
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.RotateRight
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.SignExtend
import LeanSAT.BitBlast.BVExpr.BitBlast.Impl.Mul

namespace BVExpr

def bitblast (aig : AIG BVBit) (expr : BVExpr w) : AIG.RefStreamEntry BVBit w :=
  go aig expr |>.val
where
  go {w : Nat} (aig : AIG BVBit) (expr : BVExpr w) : AIG.ExtendingRefStreamEntry aig w :=
    match expr with
    | .var a =>
      let res := bitblast.blastVar aig ⟨a⟩
      ⟨
        res,
        by
          apply AIG.LawfulStreamOperator.le_size (f := bitblast.blastVar)
      ⟩
    | .const val =>
      let res := bitblast.blastConst aig val
      ⟨
        res,
        by
          apply AIG.LawfulStreamOperator.le_size (f := bitblast.blastConst)
      ⟩
    | .zeroExtend (w := w) v inner =>
      let ⟨⟨eaig, estream⟩, heaig⟩ := go aig inner
      let res := bitblast.blastZeroExtend eaig ⟨w, estream⟩
      ⟨
        res,
        by
          apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastZeroExtend)
          dsimp at heaig
          assumption
      ⟩
    | .signExtend (w := w) v inner =>
      let ⟨⟨eaig, estream⟩, heaig⟩ := go aig inner
      let res := bitblast.blastSignExtend eaig ⟨w, estream⟩
      ⟨
        res,
        by
          apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastSignExtend)
          dsimp at heaig
          assumption
      ⟩
    | .bin lhs op rhs =>
      let ⟨⟨aig, lhs⟩, hlaig⟩ := go aig lhs
      let ⟨⟨aig, rhs⟩, hraig⟩ := go aig rhs
      let lhs := lhs.cast <| by
        dsimp at hlaig hraig
        omega
      match op with
      | .and =>
         let res := AIG.RefStream.zip aig ⟨⟨lhs, rhs⟩, AIG.mkAndCached⟩
         ⟨
           res,
           by
             apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.zip)
             dsimp at hlaig hraig
             omega
         ⟩
      | .or =>
         let res := AIG.RefStream.zip aig ⟨⟨lhs, rhs⟩, AIG.mkOrCached⟩
         ⟨
           res,
           by
             apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.zip)
             dsimp at hlaig hraig
             omega
         ⟩

      | .xor =>
         let res := AIG.RefStream.zip aig ⟨⟨lhs, rhs⟩, AIG.mkXorCached⟩
         ⟨
           res,
           by
             apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.zip)
             dsimp at hlaig hraig
             omega
         ⟩
      | .add =>
        let res := bitblast.blastAdd aig ⟨lhs, rhs⟩
        ⟨
          res,
          by
            apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastAdd)
            dsimp at hlaig hraig
            omega
        ⟩
      | .mul =>
        let res := bitblast.blastMul aig ⟨lhs, rhs⟩
        ⟨
          res,
          by
            apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastMul)
            dsimp at hlaig hraig
            omega
        ⟩
    | .un op expr =>
      let ⟨⟨eaig, estream⟩, heaig⟩ := go aig expr
      match op with
      | .not =>
          let res := bitblast.blastNot eaig estream
          ⟨
            res,
            by
              apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.map)
              dsimp at heaig
              omega
          ⟩
      | .shiftLeftConst distance =>
        let res := bitblast.blastShiftLeftConst eaig ⟨estream, distance⟩
        ⟨
          res,
          by
            apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastShiftLeftConst)
            dsimp at heaig
            assumption
        ⟩
      | .shiftRightConst distance =>
        let res := bitblast.blastShiftRightConst eaig ⟨estream, distance⟩
        ⟨
          res,
          by
            apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastShiftRightConst)
            dsimp at heaig
            assumption
        ⟩
      | .rotateLeft distance =>
        let res := bitblast.blastRotateLeft eaig ⟨estream, distance⟩
        ⟨
          res,
          by
            apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastRotateLeft)
            dsimp at heaig
            assumption
        ⟩
      | .rotateRight distance =>
        let res := bitblast.blastRotateRight eaig ⟨estream, distance⟩
        ⟨
          res,
          by
            apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastRotateRight)
            dsimp at heaig
            assumption
        ⟩
      | .arithShiftRightConst distance =>
        let res := bitblast.blastArithShiftRightConst eaig ⟨estream, distance⟩
        ⟨
          res,
          by
            apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastArithShiftRightConst)
            dsimp at heaig
            assumption
        ⟩
    | .append lhs rhs =>
      let ⟨⟨aig, lhs⟩, hlaig⟩ := go aig lhs
      let ⟨⟨aig, rhs⟩, hraig⟩ := go aig rhs
      let lhs := lhs.cast <| by
        dsimp at hlaig hraig
        omega
      let res := bitblast.blastAppend aig ⟨lhs, rhs, by ac_rfl⟩
      ⟨
        res,
        by
          apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastAppend)
          dsimp at hlaig hraig
          omega
      ⟩
    | .extract hi lo expr =>
      let ⟨⟨eaig, estream⟩, heaig⟩ := go aig expr
      let res := bitblast.blastExtract eaig ⟨estream, hi, lo, rfl⟩
      ⟨
        res,
        by
          apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastExtract)
          dsimp at heaig
          exact heaig
      ⟩
    | .shiftLeft lhs rhs => sorry


theorem bitblast_le_size {aig : AIG BVBit} (expr : BVExpr w)
    : aig.decls.size ≤ (bitblast aig expr).aig.decls.size := by
  unfold bitblast
  exact (bitblast.go aig expr).property

theorem bitblast.go_decl_eq (aig : AIG BVBit) (expr : BVExpr w)
    : ∀ (idx : Nat) (h1) (h2),
        (go aig expr).val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros idx h1 h2
  induction expr generalizing aig with
  | var =>
    dsimp [go]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastVar)]
  | const =>
    dsimp [go]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastConst)]
  | bin lhs op rhs lih rih =>
    match op with
    | .and | .or | .xor | .add | .mul =>
      dsimp [go]
      rw [AIG.LawfulStreamOperator.decl_eq]
      rw [rih, lih]
      . apply Nat.lt_of_lt_of_le
        . exact h1
        . exact (bitblast.go aig lhs).property
      . apply Nat.lt_of_lt_of_le
        . exact h1
        . apply Nat.le_trans
          . exact (bitblast.go aig lhs).property
          . exact (go (go aig lhs).1.aig rhs).property
  | un op expr ih =>
    match op with
    | .not | .shiftLeftConst .. | .shiftRightConst .. | .rotateLeft .. | .rotateRight ..
    | .arithShiftRightConst .. =>
      dsimp [go]
      rw [AIG.LawfulStreamOperator.decl_eq]
      rw [ih]
      apply Nat.lt_of_lt_of_le
      . exact h1
      . exact (go aig expr).property
  | zeroExtend w inner ih =>
    dsimp [go]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastZeroExtend)]
    rw [ih]
    apply Nat.lt_of_lt_of_le
    . exact h1
    . exact (go aig inner).property
  | signExtend w inner ih =>
    dsimp [go]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastSignExtend)]
    rw [ih]
    apply Nat.lt_of_lt_of_le
    . exact h1
    . exact (go aig inner).property
  | append lhs rhs lih rih =>
    dsimp [go]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastAppend)]
    rw [rih, lih]
    . apply Nat.lt_of_lt_of_le
      . exact h1
      . exact (bitblast.go aig lhs).property
    . apply Nat.lt_of_lt_of_le
      . exact h1
      . apply Nat.le_trans
        . exact (bitblast.go aig lhs).property
        . exact (go (go aig lhs).1.aig rhs).property
  | extract hi lo inner ih =>
    dsimp [go]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastExtract)]
    rw [ih]
    apply Nat.lt_of_lt_of_le
    . exact h1
    . exact (go aig inner).property
  | shiftLeft lhs rhs lih rih =>
    sorry


theorem bitblast_decl_eq (aig : AIG BVBit) (expr : BVExpr w)
    : ∀ (idx : Nat) (h1) (h2),
        (bitblast aig expr).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros
  unfold bitblast
  apply bitblast.go_decl_eq

instance : AIG.LawfulStreamOperator BVBit (fun _ w => BVExpr w) bitblast where
  le_size := by intros; apply bitblast_le_size
  decl_eq := by intros; apply bitblast_decl_eq

end BVExpr
