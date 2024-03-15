import LeanSAT.AIG.Gates
import LeanSAT.AIG.CachedGates
import LeanSAT.AIG.GatesLemmas

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

theorem mkNotCached_IsPrefix_env (env : Env) (gate : Nat) {hgate} :
    IsPrefix env.decls (env.mkNotCached gate hgate).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkNotCached_decl_eq
  . apply mkNotCached_le_size

@[simp]
theorem denote_mkNotCached {env : Env} {hgate} :
    ⟦env.mkNotCached gate hgate, assign⟧
      =
    ⟦env.mkNot gate hgate, assign⟧ := by
  simp [mkNot, mkNotCached]
  rw [denote_mkConstCached_lt ⟨env, gate, hgate⟩]
  rw [denote_mkConst_lt ⟨env, gate, hgate⟩]

theorem lt_mkNotCached_size (entry : Entrypoint) (gate : Nat) (hgate) : entry.start < (entry.env.mkNotCached gate hgate).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkNotCached gate hgate).env.decls.size := by
    apply mkNotCached_le_size
  omega

theorem lt_mkNotCached_size_of_lt_env_size (env : Env) (gate : Nat) (hgate) (h : x < env.decls.size)
    : x < (env.mkNotCached gate hgate).env.decls.size := by
  have := mkNotCached_le_size env gate hgate
  omega

@[simp]
theorem denote_mkNotCached_entry (entry : Entrypoint) {hgate} {h} :
    ⟦(entry.env.mkNotCached gate hgate).env, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_env_eq
  apply mkNotCached_IsPrefix_env

@[simp]
theorem denote_mkNotCached_gate (entry : Entrypoint) {hgate} {h} :
    ⟦(entry.env.mkNotCached gate hgate).env, ⟨gate, h⟩, assign⟧
      =
    ⟦entry.env, ⟨gate, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkNotCached_IsPrefix_env

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

theorem mkAndCached_IsPrefix_env (env : Env) (lhs rhs : Nat) {hl} {hr} :
    IsPrefix env.decls (env.mkAndCached lhs rhs hl hr).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkAndCached_decl_eq
  . apply mkAndCached_le_size

@[simp]
theorem denote_mkAndCached {env : Env} {hl} {hr} :
    ⟦env.mkAndCached lhs rhs hl hr, assign⟧
      =
    ⟦env.mkAnd lhs rhs hl hr, assign⟧ := by
  simp [mkAndCached]
  
theorem lt_mkAndCached_size (entry : Entrypoint) (lhs hrs : Nat) (hl) (hr)
    : entry.start < (entry.env.mkAndCached lhs rhs hl hr).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkAndCached lhs rhs hl hr).env.decls.size := by
    apply mkAndCached_le_size
  omega

theorem lt_mkAndCached_size_of_lt_env_size (env : Env) (lhs rhs : Nat) (hl hr)
    (h : x < env.decls.size)
    : x < (env.mkAndCached lhs rhs hl hr).env.decls.size := by
  have := mkAndCached_le_size env lhs rhs hl hr
  omega

@[simp]
theorem denote_mkAndCached_entry (entry : Entrypoint) {hl} {hr} {h} :
    ⟦(entry.env.mkAndCached lhs rhs hl hr).env, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_env_eq
  apply mkAndCached_IsPrefix_env

@[simp]
theorem denote_mkAndCached_lhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkAndCached lhs rhs hl hr).env, ⟨lhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨lhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkAndCached_IsPrefix_env

@[simp]
theorem denote_mkAndCached_rhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkAndCached lhs rhs hl hr).env, ⟨rhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨rhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkAndCached_IsPrefix_env

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

theorem mkOrCached_IsPrefix_env (env : Env) (lhs rhs : Nat) {hl} {hr} :
    IsPrefix env.decls (env.mkOrCached lhs rhs hl hr).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkOrCached_decl_eq
  . apply mkOrCached_le_size

@[simp]
theorem denote_mkOrCached {env : Env} {hl} {hr}:
    ⟦env.mkOrCached lhs rhs hl hr, assign⟧
      =
    ⟦env.mkOr lhs rhs hl hr, assign⟧ := by
  simp [mkOr, mkOrCached]
  
theorem lt_mkOrCached_size (entry : Entrypoint) (lhs hrs : Nat) (hl) (hr)
    : entry.start < (entry.env.mkOrCached lhs rhs hl hr).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkOrCached lhs rhs hl hr).env.decls.size := by
    apply mkOrCached_le_size
  omega

theorem lt_mkOrCached_size_of_lt_env_size (env : Env) (lhs rhs : Nat) (hl hr)
    (h : x < env.decls.size)
    : x < (env.mkOrCached lhs rhs hl hr).env.decls.size := by
  have := mkOrCached_le_size env lhs rhs hl hr
  omega

@[simp]
theorem denote_mkOrCached_lhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkOrCached lhs rhs hl hr).env, ⟨lhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨lhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkOrCached_IsPrefix_env

@[simp]
theorem denote_mkOrCached_rhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkOrCached lhs rhs hl hr).env, ⟨rhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨rhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkOrCached_IsPrefix_env

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

theorem mkXorCached_IsPrefix_env (env : Env) (lhs rhs : Nat) {hl} {hr} :
    IsPrefix env.decls (env.mkXorCached lhs rhs hl hr).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkXorCached_decl_eq
  . apply mkXorCached_le_size

@[simp]
theorem denote_mkXorCached {env : Env} {hl} {hr} :
    ⟦env.mkXorCached lhs rhs hl hr, assign⟧
      =
    ⟦env.mkXor lhs rhs hl hr, assign⟧ := by
  simp [mkXor, mkXorCached]
  -- TODO: figure out why simp doesnt pick up nicely on these
  rw [denote_mkGateCached_entry ⟨env, lhs, hl⟩]
  rw [denote_mkGate_entry ⟨env, lhs, hl⟩]
  rw [denote_mkGateCached_entry ⟨env, rhs, hr⟩]
  rw [denote_mkGate_entry ⟨env, rhs, hr⟩]

theorem lt_mkXorCached_size (entry : Entrypoint) (lhs hrs : Nat) (hl) (hr)
    : entry.start < (entry.env.mkXorCached lhs rhs hl hr).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkXorCached lhs rhs hl hr).env.decls.size := by
    apply mkXorCached_le_size
  omega

theorem lt_mkXorCached_size_of_lt_env_size (env : Env) (lhs rhs : Nat) (hl hr)
    (h : x < env.decls.size)
    : x < (env.mkXorCached lhs rhs hl hr).env.decls.size := by
  have := mkXorCached_le_size env lhs rhs hl hr
  omega

@[simp]
theorem denote_mkXorCached_lhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkXorCached lhs rhs hl hr).env, ⟨lhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨lhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkXorCached_IsPrefix_env

@[simp]
theorem denote_mkXorCached_rhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkXorCached lhs rhs hl hr).env, ⟨rhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨rhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkXorCached_IsPrefix_env

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

theorem mkBEqCached_IsPrefix_env (env : Env) (lhs rhs : Nat) {hl} {hr} :
    IsPrefix env.decls (env.mkBEqCached lhs rhs hl hr).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkBEqCached_decl_eq
  . apply mkBEqCached_le_size

@[simp]
theorem denote_mkBEqCached {env : Env} {hl} {hr} :
    ⟦env.mkBEqCached lhs rhs hl hr, assign⟧
      =
    ⟦env.mkBEq lhs rhs hl hr, assign⟧ := by
  simp [mkBEq, mkBEqCached]
  rw [denote_mkGateCached_entry ⟨env, lhs, hl⟩]
  rw [denote_mkGate_entry ⟨env, lhs, hl⟩]
  rw [denote_mkGateCached_entry ⟨env, rhs, hr⟩]
  rw [denote_mkGate_entry ⟨env, rhs, hr⟩]

theorem lt_mkBEqCached_size (entry : Entrypoint) (lhs hrs : Nat) (hl) (hr)
    : entry.start < (entry.env.mkBEqCached lhs rhs hl hr).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkBEqCached lhs rhs hl hr).env.decls.size := by
    apply mkBEqCached_le_size
  omega

theorem lt_mkBEqCached_size_of_lt_env_size (env : Env) (lhs rhs : Nat) (hl hr)
    (h : x < env.decls.size)
    : x < (env.mkBEqCached lhs rhs hl hr).env.decls.size := by
  have := mkBEqCached_le_size env lhs rhs hl hr
  omega

@[simp]
theorem denote_mkBEqCached_lhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkBEqCached lhs rhs hl hr).env, ⟨lhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨lhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkBEqCached_IsPrefix_env

@[simp]
theorem denote_mkBEqCached_rhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkBEqCached lhs rhs hl hr).env, ⟨rhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨rhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkBEqCached_IsPrefix_env

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

theorem mkImpCached_IsPrefix_env (env : Env) (lhs rhs : Nat) {hl} {hr} :
    IsPrefix env.decls (env.mkImpCached lhs rhs hl hr).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkImpCached_decl_eq
  . apply mkImpCached_le_size

@[simp]
theorem denote_mkImpCached {env : Env} {hl} {hr} :
    ⟦env.mkImpCached lhs rhs hl hr, assign⟧
      =
    ⟦env.mkImp lhs rhs hl hr, assign⟧ := by
  simp [mkImp, mkImpCached]
  
theorem lt_mkImpCached_size (entry : Entrypoint) (lhs hrs : Nat) (hl) (hr)
    : entry.start < (entry.env.mkImpCached lhs rhs hl hr).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkImpCached lhs rhs hl hr).env.decls.size := by
    apply mkImpCached_le_size
  omega

theorem lt_mkImpCached_size_of_lt_env_size (env : Env) (lhs rhs : Nat) (hl hr)
    (h : x < env.decls.size)
    : x < (env.mkImpCached lhs rhs hl hr).env.decls.size := by
  have := mkImpCached_le_size env lhs rhs hl hr
  omega

@[simp]
theorem denote_mkImpCached_lhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkImpCached lhs rhs hl hr).env, ⟨lhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨lhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkImpCached_IsPrefix_env

@[simp]
theorem denote_mkImpCached_rhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkImpCached lhs rhs hl hr).env, ⟨rhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨rhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkImpCached_IsPrefix_env

end Env
