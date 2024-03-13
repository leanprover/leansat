import LeanSAT.AIG.Cached

/--
`Env.mkGateCached` never shrinks the underlying AIG.
-/
theorem Env.mkGateCached_le_size (lhs rhs : Nat) (linv rinv : Bool) (env : Env) hl hr
    : env.decls.size ≤ (env.mkGateCached lhs rhs linv rinv hl hr).env.decls.size := by
  dsimp [mkGateCached]
  split
  . simp
  . simp_arith

/--
Reusing an `Env.Entrypoint` to build an additional gate will never invalidate the entry node of
the original entrypoint.
-/
theorem Env.lt_mkGateCached_size (e1 : Env.Entrypoint) (lhs rhs : Nat) (linv rinv : Bool) hl hr
    : e1.start < (e1.env.mkGateCached lhs rhs linv rinv hl hr).env.decls.size := by
  have h1 := e1.inv
  have h2 : e1.env.decls.size ≤ (e1.env.mkGateCached lhs rhs linv rinv hl hr).env.decls.size :=
    Env.mkGateCached_le_size _ _ _ _ _ _ _
  omega

-- TODO: refactor with denote simp things
/--
The central equality theorem between `mkGateCached` and `mkGate`.
-/
theorem Env.mkGateCached_eval_eq_mkGate_eval (lhs rhs : Nat) (linv rinv : Bool) (env : Env) (hl : lhs < env.decls.size)
    (hr : rhs < env.decls.size) :
    denote (env.mkGateCached lhs rhs linv rinv hl hr) assign = denote (env.mkGate lhs rhs linv rinv hl hr) assign := by
  simp only [mkGate, mkGateCached]
  split
  . next heq1 =>
    unfold denote denote.go
    have h1 := Cache.find?_property env.cache (.gate lhs rhs linv rinv) heq1
    simp only [Array.size_push, Nat.lt_succ_self]
    split
    . next heq2 => rw [h1] at heq2; injections
    . next heq2 => rw [h1] at heq2; injections
    . next heq2 =>
      split
      . next heq3 => rw [Array.push_get_size] at heq3; injections
      . next heq3 => rw [Array.push_get_size] at heq3; injections
      . next heq3 =>
        rw [Array.push_get_size] at heq3;
        injection heq3 with lhseq rhseq linveq rinveq
        simp only [lhseq, linveq, rhseq, rinveq]
        simp_all only [Decl.gate.injEq]
        apply ReflectSat.EvalAtAtoms.and_congr
        all_goals
          apply ReflectSat.EvalAtAtoms.xor_congr
          . rw [denote.go_lt_push]
            exact env.inv
          . rfl
  . simp [denote]

/--
`Env.mkAtomCached` never shrinks the underlying AIG.
-/
theorem Env.mkAtomCached_le_size (env : Env) (var : Nat)
    : env.decls.size ≤ (env.mkAtomCached var).env.decls.size := by
  dsimp [mkAtomCached]
  split
  . simp
  . simp_arith

-- TODO: refactor with denote simp things
/--
The central equality theorem between `mkAtomCached` and `mkAtom`.
-/
theorem Env.mkAtomCached_eval_eq_mkAtom_eval (var : Nat) (env : Env)
    : denote (env.mkAtomCached var) assign = denote (env.mkAtom var) assign := by
  simp only [mkAtom, mkAtomCached]
  split
  . next heq1 =>
    unfold denote denote.go
    have h1 := Cache.find?_property env.cache (.atom var) heq1
    simp only [Array.size_push, Nat.lt_succ_self]
    split
    . next heq2 => rw [h1] at heq2; injections
    . next heq2 =>
      split
      . next heq3 => rw [Array.push_get_size] at heq3; injections
      . next heq3 =>
        rw [Array.push_get_size] at heq3
        rw [heq2] at h1
        injections
        simp [*]
      . next heq3 => rw [Array.push_get_size] at heq3; injections
    . next heq2 => rw [h1] at heq2; injections
  . simp [denote]


/--
`Env.mkConstCached` never shrinks the underlying AIG.
-/
theorem Env.mkConstCached_le_size (env : Env) (val : Bool)
    : env.decls.size ≤ (env.mkConstCached val).env.decls.size := by
  dsimp [mkConstCached]
  split
  . simp
  . simp_arith

/--
Reusing an `Env.Entrypoint` to build an additional constant will never invalidate the entry node of
the original entrypoint.
-/
theorem Env.lt_mkConstCached_size (e1 : Env.Entrypoint) : e1.start < (e1.env.mkConstCached val).env.decls.size := by
  have h1 := e1.inv
  have h2 : e1.env.decls.size ≤ (e1.env.mkConstCached val).env.decls.size :=
    Env.mkConstCached_le_size _ _
  omega

-- TODO: refactor with denote simp things
/--
The central equality theorem between `mkConstCached` and `mkConst`.
-/
theorem Env.mkConstCached_eval_eq_mkConst_eval (val : Bool) (env : Env)
    : denote (env.mkConstCached val) assign = denote (env.mkConst val) assign := by
  simp only [mkConst, mkConstCached]
  split
  . next heq1 =>
    unfold denote denote.go
    have h1 := Cache.find?_property env.cache (.const val) heq1
    simp only [Array.size_push, Nat.lt_succ_self]
    split
    . next heq2 =>
      split
      . next heq3 =>
        rw [Array.push_get_size] at heq3
        rw [heq2] at h1
        injection heq3 with heq4
        rw [heq4] at h1
        injections
      . next heq3 => rw [Array.push_get_size] at heq3; injections
      . next heq3 => rw [Array.push_get_size] at heq3; injections
    . next heq2 => rw [h1] at heq2; injections
    . next heq2 => rw [h1] at heq2; injections
  . simp [denote]
