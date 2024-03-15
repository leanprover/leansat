import LeanSAT.AIG.CachedGates
import LeanSAT.AIG.LawfulOperator

/--
Encoding not as boolen expression in AIG form.
-/
theorem not_as_aig (b : Bool) : (true && !b) = !b := by cases b <;> decide

/--
Encoding or as boolen expression in AIG form.
-/
theorem or_as_aig (a b : Bool) : (!(!a && !b)) = (a || b) := by cases a <;> cases b <;> decide

/--
Encoding XOR as boolen expression in AIG form.
-/
theorem xor_as_aig (a b : Bool) : (!(a && b) && !(!a && !b)) = (xor a b) := by cases a <;> cases b <;> decide

/--
Encoding BEq as boolen expression in AIG form.
-/
theorem beq_as_aig (a b : Bool) : (!(a && !b) && !(!a && b)) = (a == b) := by cases a <;> cases b <;> decide

/--
Encoding implication as boolen expression in AIG form.
-/
theorem imp_as_aig (a b : Bool) : (!(a && !b)) = (!a || b) := by cases a <;> cases b <;> decide

namespace Env

theorem mkNotCached_le_size (env : Env) (gate : Nat) (hgate)
    : env.decls.size ≤ (env.mkNotCached gate hgate).env.decls.size := by
  simp only [mkNotCached]
  apply le_mkGateCached_size_of_le_env_size
  apply mkConstCached_le_size

theorem mkNotCached_decl_eq idx (env : Env) (gate : Nat) {h : idx < env.decls.size} (hgate) {h2} :
    (env.mkNotCached gate hgate).env.decls[idx]'h2 = env.decls[idx] := by
  simp only [mkNotCached]
  rw [mkGateCached_decl_eq]
  rw [mkConstCached_decl_eq]
  apply lt_mkConstCached_size_of_lt_env_size
  assumption

instance : LawfulUnaryOperator mkNotCached where
  le_size := mkNotCached_le_size
  decl_eq := by
    intros
    apply mkNotCached_decl_eq

@[simp]
theorem denote_mkNotCached {env : Env} {hgate} :
    ⟦env.mkNotCached gate hgate, assign⟧
      =
    !⟦env, ⟨gate, hgate⟩, assign⟧ := by
  rw [← not_as_aig]
  simp [mkNotCached, denote_mkConstCached_mem_prefix hgate]


theorem mkAndCached_le_size (env : Env) (lhs rhs : Nat) (hl) (hr)
    : env.decls.size ≤ (env.mkAndCached lhs rhs hl hr).env.decls.size := by
  simp only [mkAndCached]
  apply le_mkGateCached_size_of_le_env_size
  omega

theorem mkAndCached_decl_eq idx (env : Env) (lhs rhs : Nat) {h : idx < env.decls.size}
    (hl) (hr) {h2} :
    (env.mkAndCached lhs rhs hl hr).env.decls[idx]'h2 = env.decls[idx] := by
  simp only [mkAndCached]
  rw [mkGateCached_decl_eq]

instance : LawfulBinaryOperator mkAndCached where
  le_size := mkAndCached_le_size
  decl_eq := by intros; apply mkAndCached_decl_eq

@[simp]
theorem denote_mkAndCached {env : Env} {hl} {hr} :
    ⟦env.mkAndCached lhs rhs hl hr, assign⟧
      =
    (⟦env, ⟨lhs, hl⟩, assign⟧ && ⟦env, ⟨rhs, hr⟩, assign⟧) := by
  simp [mkAndCached]

theorem mkOrCached_le_size (env : Env) (lhs rhs : Nat) (hl) (hr)
    : env.decls.size ≤ (env.mkOrCached lhs rhs hl hr).env.decls.size := by
  simp only [mkOrCached]
  apply le_mkGateCached_size_of_le_env_size
  apply le_mkConstCached_size_of_le_env_size
  apply le_mkGateCached_size_of_le_env_size
  omega

theorem mkOrCached_decl_eq idx (env : Env) (lhs rhs : Nat) {h : idx < env.decls.size}
    (hl) (hr) {h2} :
    (env.mkOrCached lhs rhs hl hr).env.decls[idx]'h2 = env.decls[idx] := by
  simp only [mkOrCached]
  rw [mkGateCached_decl_eq]
  rw [mkConstCached_decl_eq]
  . rw [mkGateCached_decl_eq]
    apply lt_mkGateCached_size_of_lt_env_size
    assumption
  . apply lt_mkConstCached_size_of_lt_env_size
    apply lt_mkGateCached_size_of_lt_env_size
    assumption

instance : LawfulBinaryOperator mkOrCached where
  le_size := mkOrCached_le_size
  decl_eq := by intros; apply mkOrCached_decl_eq

@[simp]
theorem denote_mkOrCached {env : Env} {hl} {hr}:
    ⟦env.mkOrCached lhs rhs hl hr, assign⟧
      =
    (⟦env, ⟨lhs, hl⟩, assign⟧ || ⟦env, ⟨rhs, hr⟩, assign⟧) := by
  rw [← or_as_aig]
  simp [mkOrCached]

theorem mkXorCached_le_size (env : Env) (lhs rhs : Nat) (hl) (hr)
    : env.decls.size ≤ (env.mkXorCached lhs rhs hl hr).env.decls.size := by
  simp only [mkXorCached]
  apply le_mkGateCached_size_of_le_env_size
  apply le_mkGateCached_size_of_le_env_size
  apply le_mkGateCached_size_of_le_env_size
  omega

theorem mkXorCached_decl_eq idx (env : Env) (lhs rhs : Nat) {h : idx < env.decls.size}
    (hl) (hr) {h2} :
    (env.mkXorCached lhs rhs hl hr).env.decls[idx]'h2 = env.decls[idx] := by
  simp only [mkXorCached]
  rw [mkGateCached_decl_eq]
  rw [mkGateCached_decl_eq]
  . rw [mkGateCached_decl_eq]
    apply lt_mkGateCached_size_of_lt_env_size
    assumption
  . apply lt_mkGateCached_size_of_lt_env_size
    apply lt_mkGateCached_size_of_lt_env_size
    assumption

instance : LawfulBinaryOperator mkXorCached where
  le_size := mkXorCached_le_size
  decl_eq := by intros; apply mkXorCached_decl_eq

@[simp]
theorem denote_mkXorCached {env : Env} {hl} {hr} :
    ⟦env.mkXorCached lhs rhs hl hr, assign⟧
      =
    xor ⟦env, ⟨lhs, hl⟩, assign⟧ ⟦env, ⟨rhs, hr⟩, assign⟧ := by
  rw [← xor_as_aig]
  simp [mkXorCached, denote_mkGateCached_mem_prefix hl, denote_mkGateCached_mem_prefix hr]

theorem mkBEqCached_le_size (env : Env) (lhs rhs : Nat) (hl) (hr)
    : env.decls.size ≤ (env.mkBEqCached lhs rhs hl hr).env.decls.size := by
  simp only [mkBEqCached]
  apply le_mkGateCached_size_of_le_env_size
  apply le_mkGateCached_size_of_le_env_size
  apply le_mkGateCached_size_of_le_env_size
  omega

theorem mkBEqCached_decl_eq idx (env : Env) (lhs rhs : Nat) {h : idx < env.decls.size}
    (hl) (hr) {h2} :
    (env.mkBEqCached lhs rhs hl hr).env.decls[idx]'h2 = env.decls[idx] := by
  simp only [mkBEqCached]
  rw [mkGateCached_decl_eq]
  rw [mkGateCached_decl_eq]
  . rw [mkGateCached_decl_eq]
    apply lt_mkGateCached_size_of_lt_env_size
    assumption
  . apply lt_mkGateCached_size_of_lt_env_size
    apply lt_mkGateCached_size_of_lt_env_size
    assumption

instance : LawfulBinaryOperator mkBEqCached where
  le_size := mkBEqCached_le_size
  decl_eq := by intros; apply mkBEqCached_decl_eq

@[simp]
theorem denote_mkBEqCached {env : Env} {hl} {hr} :
    ⟦env.mkBEqCached lhs rhs hl hr, assign⟧
      =
    (⟦env, ⟨lhs, hl⟩, assign⟧ == ⟦env, ⟨rhs, hr⟩, assign⟧) := by
  rw [← beq_as_aig]
  simp [mkBEqCached, denote_mkGateCached_mem_prefix hl, denote_mkGateCached_mem_prefix hr]

theorem mkImpCached_le_size (env : Env) (lhs rhs : Nat) (hl) (hr)
    : env.decls.size ≤ (env.mkImpCached lhs rhs hl hr).env.decls.size := by
  simp only [mkImpCached]
  apply le_mkGateCached_size_of_le_env_size
  apply le_mkConstCached_size_of_le_env_size
  apply le_mkGateCached_size_of_le_env_size
  omega

theorem mkImpCached_decl_eq idx (env : Env) (lhs rhs : Nat) {h : idx < env.decls.size}
    (hl) (hr) {h2} :
    (env.mkImpCached lhs rhs hl hr).env.decls[idx]'h2 = env.decls[idx] := by
  simp only [mkImpCached]
  rw [mkGateCached_decl_eq]
  rw [mkConstCached_decl_eq]
  . rw [mkGateCached_decl_eq]
    apply lt_mkGateCached_size_of_lt_env_size
    assumption
  . apply lt_mkConstCached_size_of_lt_env_size
    apply lt_mkGateCached_size_of_lt_env_size
    assumption

instance : LawfulBinaryOperator mkImpCached where
  le_size := mkImpCached_le_size
  decl_eq := by intros; apply mkImpCached_decl_eq

@[simp]
theorem denote_mkImpCached {env : Env} {hl} {hr} :
    ⟦env.mkImpCached lhs rhs hl hr, assign⟧
      =
    (!⟦env, ⟨lhs, hl⟩, assign⟧ || ⟦env, ⟨rhs, hr⟩, assign⟧) := by
  rw [← imp_as_aig]
  simp [mkImpCached]

end Env
