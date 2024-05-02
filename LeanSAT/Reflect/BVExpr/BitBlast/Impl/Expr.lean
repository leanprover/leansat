import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Var
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Const
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.ShiftLeft
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.ShiftRight
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Add

namespace BVExpr

def bitblast (aig : AIG BVBit) (expr : BVExpr w) : AIG.RefStreamEntry BVBit w :=
  go aig expr |>.val
where
  go (aig : AIG BVBit) (expr : BVExpr w) : AIG.ExtendingRefStreamEntry aig w :=
    match expr with
    | .var a =>
      let res := bitblast.blastVar aig ⟨a⟩
      let aig := res.aig
      let s := res.stream
      ⟨
        ⟨aig, s⟩,
        by
          apply AIG.LawfulStreamOperator.le_size (f := bitblast.blastVar)
      ⟩
    | .const val =>
      let res := bitblast.blastConst aig val
      let aig := res.aig
      let s := res.stream
      ⟨
        ⟨aig, s⟩,
        by
          apply AIG.LawfulStreamOperator.le_size (f := bitblast.blastConst)
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
         let aig := res.aig
         let s := res.stream
         ⟨
           ⟨aig, s⟩,
           by
             apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.zip)
             dsimp at hlaig hraig
             omega
         ⟩
      | .or =>
         let res := AIG.RefStream.zip aig ⟨⟨lhs, rhs⟩, AIG.mkOrCached⟩
         let aig := res.aig
         let s := res.stream
         ⟨
           ⟨aig, s⟩,
           by
             apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.zip)
             dsimp at hlaig hraig
             omega
         ⟩

      | .xor =>
         let res := AIG.RefStream.zip aig ⟨⟨lhs, rhs⟩, AIG.mkXorCached⟩
         let aig := res.aig
         let s := res.stream
         ⟨
           ⟨aig, s⟩,
           by
             apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.zip)
             dsimp at hlaig hraig
             omega
         ⟩
      | .add =>
        let res := bitblast.blastAdd aig ⟨lhs, rhs⟩
        let aig := res.aig
        let s := res.stream
        ⟨
          ⟨aig, s⟩,
          by
            apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastAdd)
            dsimp at hlaig hraig
            omega
        ⟩
    | .un op expr =>
      let ⟨⟨eaig, estream⟩, heaig⟩ := go aig expr
      match op with
      | .not =>
          let res := AIG.RefStream.map eaig ⟨estream, AIG.mkNotCached⟩
          let aig := res.aig
          let s := res.stream
          ⟨
            ⟨aig, s⟩,
            by
              apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := AIG.RefStream.map)
              dsimp at heaig
              omega
          ⟩
      | .shiftLeftConst distance =>
        let res := bitblast.blastShiftLeftConst eaig ⟨estream, distance⟩
        let aig := res.aig
        let s := res.stream
        ⟨
          ⟨aig, s⟩,
          by
            apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastShiftLeftConst)
            dsimp at heaig
            assumption
        ⟩
      | .shiftRightConst distance =>
        let res := bitblast.blastShiftRightConst eaig ⟨estream, distance⟩
        let aig := res.aig
        let s := res.stream
        ⟨
          ⟨aig, s⟩,
          by
            apply AIG.LawfulStreamOperator.le_size_of_le_aig_size (f := bitblast.blastShiftRightConst)
            dsimp at heaig
            assumption
        ⟩

theorem bitblast_le_size {aig : AIG BVBit} (expr : BVExpr w)
    : aig.decls.size ≤ (bitblast aig expr).aig.decls.size := by
  unfold bitblast
  exact (bitblast.go aig expr).property

theorem bitblast.go_decl_eq? (aig : AIG BVBit) (expr : BVExpr w)
    : ∀ (idx : Nat) (_hidx : idx < aig.decls.size),
        (go aig expr).val.aig.decls[idx]? = aig.decls[idx]? := by
  intro idx hidx
  induction expr generalizing aig with
  | var =>
    dsimp [go]
    rw [Array.getElem?_lt, Array.getElem?_lt]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastVar)]
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastVar)
      assumption
    . assumption
  | const =>
    dsimp [go]
    rw [Array.getElem?_lt, Array.getElem?_lt]
    rw [AIG.LawfulStreamOperator.decl_eq (f := blastConst)]
    . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size (f := blastConst)
      assumption
    . assumption
  | bin lhs op rhs lih rih =>
    -- TODO: Proof dedup
    cases op
    all_goals
      dsimp [go]
      rw [Array.getElem?_lt, Array.getElem?_lt]
      rw [AIG.LawfulStreamOperator.decl_eq]
      rw [← Array.getElem?_lt, ← Array.getElem?_lt]
      rw [rih, lih]
      -- TODO: for some reason my usual omega attempts fail me here
      . assumption
      . apply Nat.lt_of_lt_of_le
        . exact hidx
        . exact (bitblast.go aig lhs).property
      . assumption
      . apply Nat.lt_of_lt_of_le
        . exact hidx
        . apply Nat.le_trans
          . exact (bitblast.go aig lhs).property
          . exact (go (go aig lhs).1.aig rhs).property
      . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size
        apply Nat.lt_of_lt_of_le
        . exact hidx
        . apply Nat.le_trans
          . exact (bitblast.go aig lhs).property
          . exact (go (go aig lhs).1.aig rhs).property
  | un op expr ih =>
    cases op
    all_goals
      dsimp [go]
      rw [Array.getElem?_lt, Array.getElem?_lt]
      rw [AIG.LawfulStreamOperator.decl_eq]
      rw [← Array.getElem?_lt, ← Array.getElem?_lt]
      rw [ih]
      . assumption
      . assumption
      . apply Nat.lt_of_lt_of_le
        . exact hidx
        . exact (go aig expr).property
      . apply AIG.LawfulStreamOperator.lt_size_of_lt_aig_size
        apply Nat.lt_of_lt_of_le
        . exact hidx
        . exact (go aig expr).property

theorem bitblast.go_decl_eq (aig : AIG BVBit) (expr : BVExpr w)
    : ∀ (idx : Nat) (h1) (h2),
        (go aig expr).val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  have := go_decl_eq? aig expr idx h1
  rw [Array.getElem?_lt, Array.getElem?_lt] at this
  injection this

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
