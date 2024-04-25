import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Var
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Const
import LeanSAT.Reflect.BVExpr.BitBlast.Impl.ShiftLeft

namespace BVExpr

def bitblast (aig : AIG BVBit) (expr : BVExpr w) : AIG.RefStreamEntry BVBit w :=
  go aig expr |>.val
where
  go (aig : AIG BVBit) (expr : BVExpr w) : AIG.ExtendingRefStreamEntry aig w :=
    match expr with
    | .var a =>
      match haig:bitblast.blastVar aig ⟨a⟩ with
      | ⟨newAig, s⟩ =>
        -- TODO: Think of a way to prettify these theorems
        ⟨
          ⟨newAig, s⟩,
          by
            have : newAig = (bitblast.blastVar aig ⟨a⟩).aig := by
              rw [haig]
            simp only [this]
            apply AIG.LawfulStreamOperator.le_size
        ⟩
    | .const val =>
      match haig:bitblast.blastConst aig val with
      | ⟨newAig, s⟩ =>
        ⟨
          ⟨newAig, s⟩,
          by
            have : newAig = (bitblast.blastConst aig val).aig := by
              simp [haig]
            simp only [this]
            apply AIG.LawfulStreamOperator.le_size
        ⟩
    | .bin lhs op rhs =>
      match go aig lhs with
      | ⟨⟨laig, lhs⟩, hlaig⟩ =>
        match go laig rhs with
        | ⟨⟨raig, rhs⟩, hraig⟩ =>
          let lhs := lhs.cast <| by
            dsimp at hlaig hraig
            omega
          match op with
          | .and =>
             match hfinal:AIG.RefStream.zip raig ⟨lhs, rhs, AIG.mkAndCached⟩ with
             | ⟨finalAig, s⟩ =>
               ⟨
                 ⟨finalAig, s⟩,
                 by
                   have : finalAig = (AIG.RefStream.zip raig ⟨lhs, rhs, AIG.mkAndCached⟩).aig := by
                     simp [hfinal]
                   simp only [this]
                   apply AIG.LawfulStreamOperator.le_size_of_le_aig_size
                   dsimp at hlaig hraig
                   omega
               ⟩
          | .or =>
             match hfinal:AIG.RefStream.zip raig ⟨lhs, rhs, AIG.mkOrCached⟩ with
             | ⟨finalAig, s⟩ =>
               ⟨
                 ⟨finalAig, s⟩,
                 by
                   have : finalAig = (AIG.RefStream.zip raig ⟨lhs, rhs, AIG.mkOrCached⟩).aig := by
                     simp [hfinal]
                   simp only [this]
                   apply AIG.LawfulStreamOperator.le_size_of_le_aig_size
                   dsimp at hlaig hraig
                   omega
               ⟩

          | .xor =>
             match hfinal:AIG.RefStream.zip raig ⟨lhs, rhs, AIG.mkXorCached⟩ with
             | ⟨finalAig, s⟩ =>
               ⟨
                 ⟨finalAig, s⟩,
                 by
                   have : finalAig = (AIG.RefStream.zip raig ⟨lhs, rhs, AIG.mkXorCached⟩).aig := by
                     simp [hfinal]
                   simp only [this]
                   apply AIG.LawfulStreamOperator.le_size_of_le_aig_size
                   dsimp at hlaig hraig
                   omega
               ⟩
    | .un op expr =>
      match go aig expr with
      | ⟨⟨eaig, estream⟩, heaig⟩ =>
        match op with
        | .not =>
            match hfinal:AIG.RefStream.map eaig ⟨estream, AIG.mkNotCached⟩ with
            | ⟨finalAig, s⟩ =>
              ⟨
                ⟨finalAig, s⟩,
                by
                  have : finalAig = (AIG.RefStream.map eaig ⟨estream, AIG.mkNotCached⟩).aig := by
                    simp [hfinal]
                  simp only [this]
                  apply AIG.LawfulStreamOperator.le_size_of_le_aig_size
                  dsimp at heaig
                  omega
              ⟩
        | .shiftLeft distance =>
          match hfinal:bitblast.blastShiftLeft eaig ⟨estream, distance⟩ with
          | ⟨finalAig, s⟩ =>
            ⟨
              ⟨finalAig, s⟩,
              by
                have : finalAig = (bitblast.blastShiftLeft eaig ⟨estream, distance⟩).aig := by
                  rw [hfinal]
                simp only [this]
                apply AIG.LawfulStreamOperator.le_size_of_le_aig_size
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
