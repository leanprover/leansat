import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Add

namespace BVExpr
namespace bitblast

structure OverflowInput (aig : AIG BVBit) where
  (w : Nat)
  stream : AIG.BinaryRefStream aig w
  cin : AIG.Ref aig

def mkOverflowBit (aig : AIG BVBit) (input : OverflowInput aig) : AIG.Entrypoint BVBit :=
  let ⟨_, ⟨lhs, rhs⟩, cin⟩ := input
  go aig 0 (by omega) cin lhs rhs
where
  go {w : Nat} (aig : AIG BVBit) (curr : Nat) (hcurr : curr ≤ w) (cin : AIG.Ref aig)
      (lhs rhs : AIG.RefStream aig w)
      : AIG.Entrypoint BVBit :=
    if hidx:curr < w then
      let lin := lhs.getRef curr hidx
      let rin := rhs.getRef curr hidx
      let res := mkFullAdderCarry aig ⟨lin, rin, cin⟩
      -- XXX: This theorem has to be stated like this for the defeq gods to be happy
      have : aig.decls.size ≤ (mkFullAdderCarry aig ⟨lhs.getRef curr hidx, rhs.getRef curr hidx, cin⟩).aig.decls.size := by
        apply AIG.LawfulOperator.le_size (f := mkFullAdderCarry)
      let aig := res.aig
      let carryRef := res.ref
      let lhs := lhs.cast this
      let rhs := rhs.cast this
      go aig (curr + 1) (by omega) carryRef lhs rhs
    else
      ⟨aig, cin⟩
  termination_by w - curr

namespace mkOverflowBit

theorem go_le_size : aig.decls.size ≤ (go aig curr hcurr cin lhs rhs).aig.decls.size := by
  unfold go
  dsimp
  split
  . refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulOperator.le_size (f := mkFullAdderCarry)
  . dsimp
    omega

theorem go_decl_eq
    : ∀ (idx : Nat) (h1) (h2),
        (go aig curr hcurr cin lhs rhs).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig curr hcurr cin lhs rhs = res
  unfold go at hgo
  dsimp at hgo
  split at hgo
  . rw [← hgo]
    intros
    rw [go_decl_eq]
    rw [AIG.LawfulOperator.decl_eq (f := mkFullAdderCarry)]
    apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := mkFullAdderCarry)
    assumption
  . simp [← hgo]

instance : AIG.LawfulOperator BVBit OverflowInput mkOverflowBit where
  le_size := by
    intros
    unfold mkOverflowBit
    dsimp
    apply go_le_size
  decl_eq := by
    intros
    unfold mkOverflowBit
    dsimp
    rw [go_decl_eq]

end mkOverflowBit

end bitblast
end BVExpr
