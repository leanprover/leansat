/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.BVExpr.Basic
import LeanSAT.AIG.CachedGatesLemmas
import LeanSAT.AIG.LawfulStreamOperator
import LeanSAT.AIG.RefStreamOperator

namespace BVExpr
namespace bitblast

variable [BEq α] [Hashable α] [DecidableEq α]

def blastNot (aig : AIG α) (s : AIG.RefStream aig w) : AIG.RefStreamEntry α w :=
  AIG.RefStream.map aig ⟨s, AIG.mkNotCached⟩

instance : AIG.LawfulStreamOperator α AIG.RefStream blastNot where
  le_size := by
    intros
    unfold blastNot
    apply AIG.LawfulStreamOperator.le_size (f := AIG.RefStream.map)
  decl_eq := by
    intros
    unfold blastNot
    apply AIG.LawfulStreamOperator.decl_eq (f := AIG.RefStream.map)

end bitblast
end BVExpr
