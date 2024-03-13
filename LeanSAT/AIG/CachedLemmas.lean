import LeanSAT.AIG.Cached

namespace Env

/--
If we find a cached gate declaration in the AIG, denoting it is equivalent to denoting `Env.mkGate`.
-/
theorem denote_mkGate_cached {env : Env} {hl} {hr}
    (h : env.cache.find? (.gate lhs rhs lpol rpol) = some gate) :
    ⟦⟨env, gate, Cache.find?_bounds env.cache (.gate lhs rhs lpol rpol) h⟩, assign⟧
      =
    ⟦env.mkGate lhs rhs lpol rpol hl hr, assign⟧ := by
  have := Cache.find?_property _ _ h
  simp only [denote_mkGate]
  conv =>
    lhs
    unfold denote denote.go
  split <;> simp_all[denote]

/--
`Env.mkGateCached` never shrinks the underlying AIG.
-/
theorem mkGateCached_le_size (lhs rhs : Nat) (linv rinv : Bool) (env : Env) hl hr
    : env.decls.size ≤ (env.mkGateCached lhs rhs linv rinv hl hr).env.decls.size := by
  dsimp [mkGateCached]
  split
  . simp
  . simp_arith

/--
Reusing an `Env.Entrypoint` to build an additional gate will never invalidate the entry node of
the original entrypoint.
-/
theorem lt_mkGateCached_size (entry : Entrypoint) (lhs rhs : Nat) (linv rinv : Bool) hl hr
    : entry.start < (entry.env.mkGateCached lhs rhs linv rinv hl hr).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkGateCached lhs rhs linv rinv hl hr).env.decls.size :=
    mkGateCached_le_size _ _ _ _ _ _ _
  omega

/--
The central equality theorem between `mkGateCached` and `mkGate`.
-/
theorem mkGateCached_eval_eq_mkGate_eval (lhs rhs : Nat) (linv rinv : Bool) (env : Env) (hl : lhs < env.decls.size)
    (hr : rhs < env.decls.size) :
    ⟦env.mkGateCached lhs rhs linv rinv hl hr, assign⟧ = ⟦env.mkGate lhs rhs linv rinv hl hr, assign⟧ := by
  simp only [mkGateCached]
  split
  . next heq1 =>
    rw [denote_mkGate_cached heq1]
  . simp [mkGate, denote]

/--
If we find a cached atom declaration in the AIG, denoting it is equivalent to denoting `Env.mkAtom`.
-/
theorem denote_mkAtom_cached {env : Env} (h : env.cache.find? (.atom v) = some gate) :
    ⟦⟨env, gate, Cache.find?_bounds env.cache (.atom v) h⟩, assign⟧ = ⟦env.mkAtom v, assign⟧ := by
  have := Cache.find?_property _ _ h
  simp only [denote_mkAtom]
  unfold denote denote.go
  split <;> simp_all

/--
`Env.mkAtomCached` never shrinks the underlying AIG.
-/
theorem mkAtomCached_le_size (env : Env) (var : Nat)
    : env.decls.size ≤ (env.mkAtomCached var).env.decls.size := by
  dsimp [mkAtomCached]
  split
  . simp
  . simp_arith

/--
The central equality theorem between `mkAtomCached` and `mkAtom`.
-/
theorem mkAtomCached_eval_eq_mkAtom_eval (var : Nat) (env : Env)
    : ⟦env.mkAtomCached var, assign⟧ = ⟦env.mkAtom var, assign⟧ := by
  simp only [mkAtomCached]
  split
  . next heq1 =>
    rw [denote_mkAtom_cached heq1]
  . simp [mkAtom, denote]

/--
If we find a cached const declaration in the AIG, denoting it is equivalent to denoting `Env.mkConst`.
-/
theorem denote_mkConst_cached {env : Env} (h : env.cache.find? (.const b) = some gate) :
    ⟦⟨env, gate, Cache.find?_bounds env.cache (.const b) h⟩, assign⟧ = ⟦env.mkConst b, assign⟧ := by
  have := Cache.find?_property _ _ h
  simp only [denote_mkConst]
  unfold denote denote.go
  split <;> simp_all

/--
`Env.mkConstCached` never shrinks the underlying AIG.
-/
theorem mkConstCached_le_size (env : Env) (val : Bool)
    : env.decls.size ≤ (env.mkConstCached val).env.decls.size := by
  dsimp [mkConstCached]
  split
  . simp
  . simp_arith

/--
Reusing an `Env.Entrypoint` to build an additional constant will never invalidate the entry node of
the original entrypoint.
-/
theorem lt_mkConstCached_size (entry : Entrypoint) : entry.start < (entry.env.mkConstCached val).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkConstCached val).env.decls.size :=
    Env.mkConstCached_le_size _ _
  omega

/--
The central equality theorem between `mkConstCached` and `mkConst`.
-/
theorem mkConstCached_eval_eq_mkConst_eval (val : Bool) (env : Env)
    : ⟦env.mkConstCached val, assign⟧ = ⟦env.mkConst val, assign⟧ := by
  simp only [mkConstCached]
  split
  . next heq1 =>
    rw [denote_mkConst_cached heq1]
  . simp [mkConst, denote]

end Env
