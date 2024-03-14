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
theorem mkGateCached_le_size (env : Env) (lhs rhs : Nat) (linv rinv : Bool) hl hr
    : env.decls.size ≤ (env.mkGateCached lhs rhs linv rinv hl hr).env.decls.size := by
  dsimp [mkGateCached]
  split
  . simp
  . simp_arith

theorem lt_mkGateCached_size_of_lt_env_size (entry : Entrypoint) (lhs rhs : Nat) (linv rinv : Bool) (hl) (hr) (h : x < entry.env.decls.size)
    : x < (entry.env.mkGateCached lhs rhs linv rinv hl hr).env.decls.size := by
  have := mkGateCached_le_size entry.env lhs rhs linv rinv hl hr
  omega

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
`mkGateCached` does not modify the input AIG upon a cache hit.
-/
theorem mkGateCached_hit_env (env : Env) (hcache : env.cache.find? (.gate lhs rhs linv rinv) = some gate) (hl) (hr) :
    (env.mkGateCached lhs rhs linv rinv hl hr).env = env := by
  simp only [mkGateCached]
  split <;> simp_all

/--
`mkGateCached` pushes to the input AIG upon a cache miss.
-/
theorem mkGateCached_miss_env (env : Env) (hcache : env.cache.find? (.gate lhs rhs linv rinv) = none) (hl) (hr) :
    (env.mkGateCached lhs rhs linv rinv hl hr).env.decls = env.decls.push (.gate lhs rhs linv rinv) := by
  simp only [mkGateCached]
  split <;> simp_all

/--
The AIG produced by `Env.mkGateCached` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkGateCached_decl_eq idx (env : Env) (lhs rhs : Nat) (linv rinv : Bool)
    {h : idx < env.decls.size} {hl} {hr} {hbound} :
    (env.mkGateCached lhs rhs linv rinv hl hr).env.decls[idx]'hbound = env.decls[idx] := by
  match hcache:env.cache.find? (.gate lhs rhs linv rinv) with
  | some gate =>
    have := mkGateCached_hit_env env hcache hl hr
    simp [this]
  | none =>
    have := mkGateCached_miss_env env hcache hl hr
    simp only [this, Array.get_push]
    split
    . rfl
    . contradiction

/--
The input AIG to an `Env.mkGateCached` is a prefix to the output AIG.
-/
theorem mkGateCached_IsPrefix_env {env : Env} {hl} {hr} :
    IsPrefix env.decls (env.mkGateCached lhs rhs lpol rpol hl hr).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkGateCached_decl_eq
  . apply mkGateCached_le_size

@[simp]
theorem denote_mkGateCached_entry (entry : Entrypoint) {hlbound} {hrbound} {h} :
    ⟦(entry.env.mkGateCached lhs rhs lpol rpol hlbound hrbound).env, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_env_eq
  apply mkGateCached_IsPrefix_env

@[simp]
theorem denote_mkGateCached_lhs (entry : Entrypoint) {hlbound} {hrbound} {h} :
    ⟦(entry.env.mkGateCached lhs rhs lpol rpol hlbound hrbound).env, ⟨lhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨lhs, hlbound⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkGateCached_IsPrefix_env

@[simp]
theorem denote_mkGateCached_rhs (entry : Entrypoint) {hlbound} {hrbound} {h} :
    ⟦(entry.env.mkGateCached lhs rhs lpol rpol hlbound hrbound).env, ⟨rhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨rhs, hrbound⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkGateCached_IsPrefix_env

/--
The central equality theorem between `mkGateCached` and `mkGate`.
-/
@[simp]
theorem mkGateCached_eval_eq_mkGate_eval {env : Env} {hl} {hr} :
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
`mkAtomCached` does not modify the input AIG upon a cache hit.
-/
theorem mkAtomCached_hit_env (env : Env) (hcache : env.cache.find? (.atom var) = some gate) :
    (env.mkAtomCached var).env = env := by
  simp only [mkAtomCached]
  split <;> simp_all

/--
`mkAtomCached` pushes to the input AIG upon a cache miss.
-/
theorem mkAtomCached_miss_env (env : Env) (hcache : env.cache.find? (.atom var) = none) :
    (env.mkAtomCached var).env.decls = env.decls.push (.atom var) := by
  simp only [mkAtomCached]
  split <;> simp_all

/--
The AIG produced by `Env.mkAtomCached` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkAtomCached_decl_eq (env : Env) (var : Nat) (idx : Nat) {h : idx < env.decls.size} {hbound} :
    (env.mkAtomCached var).env.decls[idx]'hbound = env.decls[idx] := by
  match hcache:env.cache.find? (.atom var) with
  | some gate =>
    have := mkAtomCached_hit_env env hcache
    simp [this]
  | none =>
    have := mkAtomCached_miss_env env hcache
    simp only [this, Array.get_push]
    split
    . rfl
    . contradiction

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
@[simp]
theorem mkAtomCached_eval_eq_mkAtom_eval {env : Env}
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
`mkConstCached` does not modify the input AIG upon a cache hit.
-/
theorem mkConstCached_hit_env (env : Env) (hcache : env.cache.find? (.const val) = some gate) :
    (env.mkConstCached val).env = env := by
  simp only [mkConstCached]
  split <;> simp_all

/--
`mkConstCached` pushes to the input AIG upon a cache miss.
-/
theorem mkConstCached_miss_env (env : Env) (hcache : env.cache.find? (.const val) = none) :
    (env.mkConstCached val).env.decls = env.decls.push (.const val) := by
  simp only [mkConstCached]
  split <;> simp_all

/--
The AIG produced by `Env.mkConstCached` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkConstCached_decl_eq (env : Env) (val : Bool) (idx : Nat) {h : idx < env.decls.size} {hbound} :
    (env.mkConstCached val).env.decls[idx]'hbound = env.decls[idx] := by
  match hcache:env.cache.find? (.const val) with
  | some gate =>
    have := mkConstCached_hit_env env hcache
    simp [this]
  | none =>
    have := mkConstCached_miss_env env hcache
    simp only [this, Array.get_push]
    split
    . rfl
    . contradiction

/--
`Env.mkConstCached` never shrinks the underlying AIG.
-/
theorem mkConstCached_le_size (env : Env) (val : Bool)
    : env.decls.size ≤ (env.mkConstCached val).env.decls.size := by
  dsimp [mkConstCached]
  split
  . simp
  . simp_arith

theorem lt_mkConstCached_size_of_lt_env_size (entry : Entrypoint) (val : Bool) (h : x < entry.env.decls.size) :
    x < (entry.env.mkConstCached val).env.decls.size := by
  have := mkConstCached_le_size entry.env val
  omega

/--
Reusing an `Env.Entrypoint` to build an additional constant will never invalidate the entry node of
the original entrypoint.
-/
theorem lt_mkConstCached_size (entry : Entrypoint) : entry.start < (entry.env.mkConstCached val).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkConstCached val).env.decls.size :=
    Env.mkConstCached_le_size _ _
  omega

theorem mkConstCached_IsPrefix_env : IsPrefix env.decls (mkConstCached val env).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkConstCached_decl_eq
  . apply mkConstCached_le_size

@[simp]
theorem denote_mkConstCached_lt (entry : Entrypoint) {h} :
    ⟦(entry.env.mkConstCached val).env, ⟨entry.start, h⟩, assign⟧
      =
    ⟦entry, assign⟧ := by
  apply denote.eq_of_env_eq
  apply mkConstCached_IsPrefix_env

/--
The central equality theorem between `mkConstCached` and `mkConst`.
-/
@[simp]
theorem mkConstCached_eval_eq_mkConst_eval {env : Env}
    : ⟦env.mkConstCached val, assign⟧ = ⟦env.mkConst val, assign⟧ := by
  simp only [mkConstCached]
  split
  . next heq1 =>
    rw [denote_mkConst_cached heq1]
  . simp [mkConst, denote]

end Env
