import LeanSAT.AIG.Basic

/--
Running `Env.denote.go` on a node that is within bounds of `decls` is equivalent to running it a bigger `decls` array.
-/
theorem Env.denote.go_lt_push (x : Nat) (decls : Array Decl) (h1 : x < decls.size) {h2} {h3} (inv : IsDag decls) :
    (denote.go x decls assign h1 h2) = (denote.go x (decls.push decl) assign (by simp; omega) h3) := by
  unfold denote.go
  simp [h1]
  have h4 := Array.push_get_old decls decl h1
  split
  . next heq1 =>
    split
    all_goals
      next heq2 =>
        rw [h4, heq1] at heq2;
        injections
  . next heq1 =>
    split
    . next heq2 => rw [h4, heq1] at heq2; injections
    . next heq2 => rw [h4, heq1] at heq2; injection heq2 with heq3; simp [heq3]
    . next heq2 => rw [h4, heq1] at heq2; injections
  . next lhs1 rhs1 linv1 rinv1 heq1 =>
    split
    . next heq2 => rw [h4, heq1] at heq2; injections
    . next heq2 => rw [h4, heq1] at heq2; injections
    . next lhs2 rhs2 linv2 rinv2 heq2 =>
      rw [heq1, heq2] at h4
      injection h4 with lhseq rhseq linveq rinveq
      simp only [lhseq, linveq, rhseq, rinveq]
      have := inv x lhs1 rhs1 linv1 rinv1 h1 heq1
      apply ReflectSat.EvalAtAtoms.and_congr
      all_goals
        apply ReflectSat.EvalAtAtoms.xor_congr
        . apply denote.go_lt_push
          assumption
        . rfl
termination_by sizeOf x

theorem Env.denote.go_eq_of_env_eq (decls1 decls2 : Array Decl) {hdag1} {hdag2} {hbounds}
    (hsize : decls1.size ≤ decls2.size)
    (hidx : ∀ idx (h : idx < decls1.size), decls2[idx]'(by omega) = decls1[idx]'h) :
    denote.go start decls2 assign (by omega) hdag2
      =
    denote.go start decls1 assign hbounds hdag1 := by
  unfold denote.go
  have hidx1 := hidx start hbounds
  split
  . next heq =>
    rw [hidx1] at heq
    split <;> simp_all
  . next heq =>
    rw [hidx1] at heq
    split <;> simp_all
  . next lhs rhs linv rinv heq =>
    rw [hidx1] at heq
    have foo := hdag1 start lhs rhs linv rinv hbounds heq
    have hidx2 := hidx lhs (by omega)
    have hidx3 := hidx rhs (by omega)
    split
    . simp_all
    . simp_all
    . simp_all
      apply ReflectSat.EvalAtAtoms.and_congr
      all_goals
        apply ReflectSat.EvalAtAtoms.xor_congr
        . apply Env.denote.go_eq_of_env_eq
          . exact hidx
          . exact hsize
        . rfl
termination_by sizeOf start

theorem Env.denote.eq_of_env_eq (entry : Entrypoint) (newEnv : Env)
    (hsize : entry.env.decls.size ≤ newEnv.decls.size)
    (hidx : ∀ idx (h : idx < entry.env.decls.size), newEnv.decls[idx]'(by omega) = entry.env.decls[idx]'h)
    {hbounds} :
    denote ⟨newEnv, entry.start, hbounds⟩ assign
      =
    denote entry assign := by
  unfold denote
  apply Env.denote.go_eq_of_env_eq
  exact hidx
  exact hsize

@[simp]
theorem Env.denote_projected_entry {entry : Env.Entrypoint} :
    denote ⟨entry.env, entry.start, entry.inv⟩ assign = denote entry assign := by
  cases entry; simp

/--
`Env.mkGate` never shrinks the underlying AIG.
-/
theorem Env.mkGate_le_size (lhs rhs : Nat) (linv rinv : Bool) (env : Env) hl hr
    : env.decls.size ≤ (env.mkGate lhs rhs linv rinv hl hr).env.decls.size := by
  simp_arith [mkGate]

theorem Env.mkGate_decl_eq idx (h : idx < env.decls.size) {hbound} :
    (mkGate lhs rhs linv rinv env hl hr).env.decls[idx]'hbound = env.decls[idx] := by
  simp only [mkGate, Array.push_get]
  split
  . rfl
  . contradiction

@[simp]
theorem Env.denote_mkGate :
    denote (mkGate lhs rhs linv rinv env hl hr) assign
      =
    ((xor (denote ⟨env, lhs, hl⟩ assign) linv) && (xor (denote ⟨env, rhs, hr⟩ assign) rinv)) := by
  conv =>
    lhs
    unfold denote denote.go
  split
  . next heq =>
    rw [mkGate, Array.push_get_size] at heq
    contradiction
  . next heq =>
    rw [mkGate, Array.push_get_size] at heq
    contradiction
  . next heq =>
    rw [mkGate, Array.push_get_size] at heq
    injection heq with heq1 heq2 heq3 heq4
    simp
    apply ReflectSat.EvalAtAtoms.and_congr
    all_goals
      apply ReflectSat.EvalAtAtoms.xor_congr
      . unfold denote
        simp only [heq1, heq2]
        apply Env.denote.go_eq_of_env_eq
        . intro idx h; apply mkGate_decl_eq
        . apply mkGate_le_size
      . simp only [heq3, heq4]

/--
Reusing an `Env.Entrypoint` to build an additional gate will never invalidate the entry node of
the original entrypoint.
-/
theorem Env.lt_mkGate_size (e1 : Env.Entrypoint) (lhs rhs : Nat) (linv rinv : Bool) hl hr
    : e1.start < (e1.env.mkGate lhs rhs linv rinv hl hr).env.decls.size := by
  have h1 := e1.inv
  have h2 : e1.env.decls.size ≤ (e1.env.mkGate lhs rhs linv rinv hl hr).env.decls.size :=
    Env.mkGate_le_size _ _ _ _ _ _ _
  omega

/--
`Env.mkAtom` never shrinks the underlying AIG.
-/
theorem Env.mkAtom_le_size (env : Env) (var : Nat)
    : env.decls.size ≤ (env.mkAtom var).env.decls.size := by
  simp_arith [mkAtom]

theorem Env.mkAtom_decl_eq idx (h : idx < env.decls.size) {hbound} :
    (mkAtom var env ).env.decls[idx]'hbound = env.decls[idx] := by
  simp only [mkAtom, Array.push_get]
  split
  . rfl
  . contradiction

@[simp]
theorem Env.denote_mkAtom : denote (mkAtom var env) assign = assign.getD var false := by
  unfold denote denote.go
  split
  . next heq =>
    rw [mkAtom, Array.push_get_size] at heq
    contradiction
  . next heq =>
    rw [mkAtom, Array.push_get_size] at heq
    injection heq with heq
    rw [heq]
  . next heq =>
    rw [mkAtom, Array.push_get_size] at heq
    contradiction

theorem Env.mkConst_decl_eq idx (h : idx < env.decls.size) {hbound} :
    (mkConst val env).env.decls[idx]'hbound = env.decls[idx] := by
  simp only [mkConst, Array.push_get]
  split
  . rfl
  . contradiction

/--
`Env.mkConst` never shrinks the underlying AIG.
-/
theorem Env.mkConst_le_size (env : Env) (val : Bool)
    : env.decls.size ≤ (env.mkConst val).env.decls.size := by
  simp_arith [mkConst]

@[simp]
theorem Env.denote_mkConst : denote (mkConst val env) assign = val := by
  unfold denote denote.go
  split
  . next heq =>
    rw [mkConst, Array.push_get_size] at heq
    injection heq with heq
    rw [heq]
  . next heq =>
    rw [mkConst, Array.push_get_size] at heq
    contradiction
  . next heq =>
    rw [mkConst, Array.push_get_size] at heq
    contradiction

@[simp]
theorem Env.denote_mkConst_lt (entry : Env.Entrypoint) {h} :
    denote ⟨(mkConst val entry.env).env, entry.start, h⟩ assign = denote entry assign :=  by
  apply Env.denote.go_eq_of_env_eq
  . intro idx h
    apply mkConst_decl_eq
  . apply mkConst_le_size

/--
Reusing an `Env.Entrypoint` to build an additional constant will never invalidate the entry node of
the original entrypoint.
-/
theorem Env.lt_mkConst_size (e1 : Env.Entrypoint) : e1.start < (e1.env.mkConst val).env.decls.size := by
  have h1 := e1.inv
  have h2 : e1.env.decls.size ≤ (e1.env.mkConst val).env.decls.size :=
    Env.mkConst_le_size _ _
  omega
