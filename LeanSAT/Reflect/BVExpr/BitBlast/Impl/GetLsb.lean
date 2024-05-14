import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Expr

namespace BVPred

structure GetLsbTarget where
  {w : Nat}
  expr : BVExpr w
  idx : Nat

def blastGetLsb (aig : AIG BVBit) (target : GetLsbTarget) : AIG.Entrypoint BVBit :=
  if h:target.idx < target.w then
    -- Note: This blasts the entire rexpression up to `w` despite only needing it up to `idx`.
    -- However the vast majority of operations are interested in all bits so the API is currently
    -- not designed to support this use case.
    let res := target.expr.bitblast aig
    let aig := res.aig
    let stream := res.stream
    ⟨aig, stream.getRef target.idx h⟩
  else
    AIG.mkConstCached aig false

instance : AIG.LawfulOperator BVBit (fun _ => GetLsbTarget) blastGetLsb where
  le_size := by
    intros
    unfold blastGetLsb
    dsimp
    split
    . apply AIG.LawfulStreamOperator.le_size (f := BVExpr.bitblast)
    . apply AIG.LawfulOperator.le_size (f := AIG.mkConstCached)
  decl_eq := by
    intros
    unfold blastGetLsb
    dsimp
    split
    . rw [AIG.LawfulStreamOperator.decl_eq (f := BVExpr.bitblast)]
    . rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]

end BVPred
