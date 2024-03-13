import LeanSAT.AIG.Basic

namespace Env

structure IsPrefix (decls1 decls2 : Array Decl) : Prop where
  size_le : decls1.size ≤ decls2.size
  idx_eq : ∀ idx (h : idx < decls1.size), decls2[idx]'(by omega) = decls1[idx]'h

theorem IsPrefix.of {decls1 decls2 : Array Decl}
    (size_le : decls1.size ≤ decls2.size)
    (idx_eq : ∀ idx (h : idx < decls1.size), decls2[idx]'(by omega) = decls1[idx]'h)
    : IsPrefix decls1 decls2 := ⟨size_le, idx_eq⟩

/--
If `decls1` is a prefix of `decls2` and we start evaluating `decls2` at an
index in bounds of `decls1` we can evluate at `decls1`.
-/
theorem denote.go_eq_of_env_eq (decls1 decls2 : Array Decl) (start : Nat) {hdag1} {hdag2}
    {hbounds1} {hbounds2} (hprefix : IsPrefix decls1 decls2) :
    denote.go start decls2 assign hbounds2 hdag2
      =
    denote.go start decls1 assign hbounds1 hdag1 := by
  unfold denote.go
  have hidx1 := hprefix.idx_eq start hbounds1
  split
  . next heq =>
    rw [hidx1] at heq
    split <;> simp_all
  . next heq =>
    rw [hidx1] at heq
    split <;> simp_all
  . next lhs rhs linv rinv heq =>
    rw [hidx1] at heq
    have foo := hdag1 start lhs rhs linv rinv hbounds1 heq
    have hidx2 := hprefix.idx_eq lhs (by omega)
    have hidx3 := hprefix.idx_eq rhs (by omega)
    split
    . simp_all
    . simp_all
    . simp_all
      apply ReflectSat.EvalAtAtoms.and_congr
      all_goals
        apply ReflectSat.EvalAtAtoms.xor_congr
        . apply denote.go_eq_of_env_eq
          assumption
        . rfl
termination_by sizeOf start

/--
Running `Env.denote.go` on a node that is within bounds of `decls` is equivalent to running it a bigger `decls` array.
-/
theorem denote.go_lt_push (x : Nat) (decls : Array Decl) {h1} {h2} {h3} :
    (denote.go x (decls.push decl) assign (by simp; omega) h3) = (denote.go x decls assign h1 h2)  := by
  apply denote.go_eq_of_env_eq
  apply IsPrefix.of
  . intro idx h
    simp only [Array.push_get]
    split
    . rfl
    . contradiction
  . simp_arith

@[inherit_doc denote.go_eq_of_env_eq ]
theorem denote.eq_of_env_eq (entry : Entrypoint) (newEnv : Env) (hprefix : IsPrefix entry.env.decls newEnv.decls)
    {hbounds} :
    ⟦newEnv, ⟨entry.start, hbounds⟩, assign⟧
      =
    ⟦entry, assign⟧
    := by
  unfold denote
  apply denote.go_eq_of_env_eq
  assumption

@[simp]
theorem denote_projected_entry {entry : Env.Entrypoint} :
    ⟦entry.env, ⟨entry.start, entry.inv⟩, assign⟧ = ⟦entry, assign⟧ := by
  cases entry; simp

/--
`Env.mkGate` never shrinks the underlying AIG.
-/
theorem mkGate_le_size (env : Env) (lhs rhs : Nat) (linv rinv : Bool) (hl) (hr)
    : env.decls.size ≤ (env.mkGate lhs rhs linv rinv hl hr).env.decls.size := by
  simp_arith [mkGate]

/--
The AIG produced by `Env.mkGate` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkGate_decl_eq idx (env : Env) (lhs rhs : Nat) (linv rinv : Bool) {h : idx < env.decls.size} {hl} {hr} :
    (env.mkGate lhs rhs linv rinv hl hr).env.decls[idx]'(by simp[mkGate]; omega) = env.decls[idx] := by
  simp only [mkGate, Array.push_get]
  split
  . rfl
  . contradiction

/--
The input AIG to an `mkGate` is a prefix to the output AIG.
-/
theorem mkGate_IsPrefix_env (env : Env) (lhs rhs : Nat) (linv rinv : Bool) {hl} {hr} :
    IsPrefix env.decls (env.mkGate lhs rhs linv rinv hl hr).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkGate_decl_eq
  . apply mkGate_le_size

@[simp]
theorem denote_mkGate :
    ⟦env.mkGate lhs rhs linv rinv hl hr, assign⟧
      =
    ((xor ⟦env, ⟨lhs, hl⟩, assign⟧ linv) && (xor ⟦env, ⟨rhs, hr⟩, assign⟧ rinv)) := by
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
        apply denote.go_eq_of_env_eq
        apply mkGate_IsPrefix_env
      . simp only [heq3, heq4]

/--
Reusing an `Env.Entrypoint` to build an additional gate will never invalidate the entry node of
the original entrypoint.
-/
theorem lt_mkGate_size (entry : Entrypoint) (lhs rhs : Nat) (linv rinv : Bool) {hl} {hr}
    : entry.start < (entry.env.mkGate lhs rhs linv rinv hl hr).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkGate lhs rhs linv rinv hl hr).env.decls.size := by
    apply mkGate_le_size
  omega

@[simp]
theorem denote_mkGate_entry (entry : Entrypoint) {hlbound} {hrbound} {h} :
    ⟦(entry.env.mkGate lhs rhs lpol rpol hlbound hrbound).env, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_env_eq
  apply mkGate_IsPrefix_env

@[simp]
theorem denote_mkGate_lhs (entry : Entrypoint) {hlbound} {hrbound} {h} :
    ⟦(entry.env.mkGate lhs rhs lpol rpol hlbound hrbound).env, ⟨lhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨lhs, hlbound⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkGate_IsPrefix_env
  . assumption
  . assumption

@[simp]
theorem denote_mkGate_rhs (entry : Entrypoint) {hlbound} {hrbound} {h} :
    ⟦(entry.env.mkGate lhs rhs lpol rpol hlbound hrbound).env, ⟨rhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨rhs, hrbound⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkGate_IsPrefix_env
  . assumption
  . assumption

/--
`Env.mkAtom` never shrinks the underlying AIG.
-/
theorem mkAtom_le_size (env : Env) (var : Nat) : env.decls.size ≤ (env.mkAtom var).env.decls.size := by
  simp_arith [mkAtom]

/--
The AIG produced by `Env.mkAtom` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkAtom_decl_eq (env : Env) (var : Nat) (idx : Nat) {h : idx < env.decls.size} {hbound} :
    (env.mkAtom var).env.decls[idx]'hbound = env.decls[idx] := by
  simp only [mkAtom, Array.push_get]
  split
  . rfl
  . contradiction

/--
The input AIG to an `mkAtom` is a prefix to the output AIG.
-/
theorem mkAtom_IsPrefix_env (env : Env) (var : Nat) :
    IsPrefix env.decls (env.mkAtom var).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkAtom_decl_eq
  . apply mkAtom_le_size

@[simp]
theorem denote_mkAtom {env : Env} :
    ⟦(env.mkAtom var), assign⟧ = assign.getD var false := by
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

@[simp]
theorem denote_mkAtom_lt (entry : Entrypoint) {h} :
    ⟦(entry.env.mkAtom var).env, ⟨entry.start, h⟩, assign⟧
      =
    ⟦entry, assign⟧ := by
  apply denote.eq_of_env_eq
  apply mkAtom_IsPrefix_env

/--
The AIG produced by `Env.mkConst` agrees with the input AIG on all indices that are valid for both.
-/
theorem mkConst_decl_eq (env : Env) (val : Bool) (idx : Nat) {h : idx < env.decls.size} {hbound} :
    (env.mkConst val).env.decls[idx]'hbound = env.decls[idx] := by
  simp only [mkConst, Array.push_get]
  split
  . rfl
  . contradiction

/--
`Env.mkConst` never shrinks the underlying AIG.
-/
theorem mkConst_le_size (env : Env) (val : Bool)
    : env.decls.size ≤ (env.mkConst val).env.decls.size := by
  simp_arith [mkConst]

/--
The input AIG to an `mkConst` is a prefix to the output AIG.
-/
theorem mkConst_IsPrefix_env (env : Env) (const : Bool) :
    IsPrefix env.decls (env.mkConst const).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkConst_decl_eq
  . apply mkConst_le_size

@[simp]
theorem denote_mkConst {env : Env} : ⟦(env.mkConst val), assign⟧ = val := by
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
theorem denote_mkConst_lt (entry : Entrypoint) {h} :
    ⟦(entry.env.mkConst val).env, ⟨entry.start, h⟩, assign⟧
      =
    ⟦entry, assign⟧ := by
  apply denote.eq_of_env_eq
  apply mkConst_IsPrefix_env

/--
Reusing an `Env.Entrypoint` to build an additional constant will never invalidate the entry node of
the original entrypoint.
-/
theorem lt_mkConst_size (entry : Entrypoint) (val : Bool) : entry.start < (entry.env.mkConst val).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkConst val).env.decls.size :=
    mkConst_le_size _ _
  omega

end Env
