import LeanSAT.AIG.Gates

theorem not_as_and (b : Bool) : (true && !b) = !b := by cases b <;> decide
theorem or_as_and (a b : Bool) : (!(!a && !b)) = (a || b) := by cases a <;> cases b <;> decide
theorem xor_as_and (a b : Bool) : (!(a && b) && !(!a && !b)) = (xor a b) := by cases a <;> cases b <;> decide
theorem beq_as_and (a b : Bool) : (!(a && !b) && !(!a && b)) = (a == b) := by cases a <;> cases b <;> decide
theorem imp_as_and (a b : Bool) : (!(a && !b)) = (!a || b) := by cases a <;> cases b <;> decide

namespace Env

theorem mkNot_le_size (env : Env) (gate : Nat) (hgate)
    : env.decls.size ≤ (env.mkNot gate hgate).env.decls.size := by
  simp only [mkNot]
  apply le_mkGate_size_of_le_env_size
  apply mkConst_le_size

theorem mkNot_decl_eq idx (env : Env) (gate : Nat) {h : idx < env.decls.size} (hgate) {h2} :
    (env.mkNot gate hgate).env.decls[idx]'h2 = env.decls[idx] := by
  simp only [mkNot]
  rw [mkGate_decl_eq]
  rw [mkConst_decl_eq]
  apply lt_mkConst_size_of_lt_env_size
  assumption

theorem mkNot_IsPrefix_env (env : Env) (gate : Nat) {hgate} :
    IsPrefix env.decls (env.mkNot gate hgate).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkNot_decl_eq
  . apply mkNot_le_size

@[simp]
theorem denote_mkNot :
    ⟦env.mkNot gate hgate, assign⟧
      =
    !⟦env, ⟨gate, hgate⟩, assign⟧ := by
  rw [← not_as_and]
  simp [mkNot]
  rw [denote_mkConst_lt ⟨env, gate, hgate⟩]

theorem lt_mkNot_size (entry : Entrypoint) (gate : Nat) (hgate) : entry.start < (entry.env.mkNot gate hgate).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkNot gate hgate).env.decls.size := by
    apply mkNot_le_size
  omega

theorem lt_mkNot_size_of_lt_env_size (env : Env) (gate : Nat) (hgate) (h : x < env.decls.size)
    : x < (env.mkNot gate hgate).env.decls.size := by
  have := mkNot_le_size env gate hgate
  omega

@[simp]
theorem denote_mkNot_entry (entry : Entrypoint) {hgate} {h} :
    ⟦(entry.env.mkNot gate hgate).env, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_env_eq
  apply mkNot_IsPrefix_env

@[simp]
theorem denote_mkNot_gate (entry : Entrypoint) {hgate} {h} :
    ⟦(entry.env.mkNot gate hgate).env, ⟨gate, h⟩, assign⟧
      =
    ⟦entry.env, ⟨gate, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkNot_IsPrefix_env
  assumption

theorem mkAnd_le_size (env : Env) (lhs rhs : Nat) (hl) (hr)
    : env.decls.size ≤ (env.mkAnd lhs rhs hl hr).env.decls.size := by
  simp only [mkAnd]
  apply le_mkGate_size_of_le_env_size
  omega

theorem mkAnd_decl_eq idx (env : Env) (lhs rhs : Nat) {h : idx < env.decls.size}
    (hl) (hr) {h2} :
    (env.mkAnd lhs rhs hl hr).env.decls[idx]'h2 = env.decls[idx] := by
  simp only [mkAnd]
  rw [mkGate_decl_eq]

theorem mkAnd_IsPrefix_env (env : Env) (lhs rhs : Nat) {hl} {hr} :
    IsPrefix env.decls (env.mkAnd lhs rhs hl hr).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkAnd_decl_eq
  . apply mkAnd_le_size

@[simp]
theorem denote_mkAnd :
    ⟦env.mkAnd lhs rhs hl hr, assign⟧
      =
    (⟦env, ⟨lhs, hl⟩, assign⟧ && ⟦env, ⟨rhs, hr⟩, assign⟧) := by
  simp [mkAnd]
  
theorem lt_mkAnd_size (entry : Entrypoint) (lhs hrs : Nat) (hl) (hr)
    : entry.start < (entry.env.mkAnd lhs rhs hl hr).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkAnd lhs rhs hl hr).env.decls.size := by
    apply mkAnd_le_size
  omega

theorem lt_mkAnd_size_of_lt_env_size (env : Env) (lhs rhs : Nat) (hl hr)
    (h : x < env.decls.size)
    : x < (env.mkAnd lhs rhs hl hr).env.decls.size := by
  have := mkAnd_le_size env lhs rhs hl hr
  omega

@[simp]
theorem denote_mkAnd_entry (entry : Entrypoint) {hl} {hr} {h} :
    ⟦(entry.env.mkAnd lhs rhs hl hr).env, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_env_eq
  apply mkAnd_IsPrefix_env

@[simp]
theorem denote_mkAnd_lhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkAnd lhs rhs hl hr).env, ⟨lhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨lhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkAnd_IsPrefix_env
  . assumption
  . assumption

@[simp]
theorem denote_mkAnd_rhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkAnd lhs rhs hl hr).env, ⟨rhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨rhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkAnd_IsPrefix_env
  . assumption
  . assumption

theorem mkOr_le_size (env : Env) (lhs rhs : Nat) (hl) (hr)
    : env.decls.size ≤ (env.mkOr lhs rhs hl hr).env.decls.size := by
  simp only [mkOr]
  apply le_mkGate_size_of_le_env_size
  apply le_mkConst_size_of_le_env_size
  apply le_mkGate_size_of_le_env_size
  omega

theorem mkOr_decl_eq idx (env : Env) (lhs rhs : Nat) {h : idx < env.decls.size}
    (hl) (hr) {h2} :
    (env.mkOr lhs rhs hl hr).env.decls[idx]'h2 = env.decls[idx] := by
  simp only [mkOr]
  rw [mkGate_decl_eq]
  rw [mkConst_decl_eq]
  rw [mkGate_decl_eq]
  apply lt_mkConst_size_of_lt_env_size
  apply lt_mkGate_size_of_lt_env_size
  assumption

theorem mkOr_IsPrefix_env (env : Env) (lhs rhs : Nat) {hl} {hr} :
    IsPrefix env.decls (env.mkOr lhs rhs hl hr).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkOr_decl_eq
  . apply mkOr_le_size

@[simp]
theorem denote_mkOr :
    ⟦env.mkOr lhs rhs hl hr, assign⟧
      =
    (⟦env, ⟨lhs, hl⟩, assign⟧ || ⟦env, ⟨rhs, hr⟩, assign⟧) := by
  rw [← or_as_and]
  simp [mkOr]
  
theorem lt_mkOr_size (entry : Entrypoint) (lhs hrs : Nat) (hl) (hr)
    : entry.start < (entry.env.mkOr lhs rhs hl hr).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkOr lhs rhs hl hr).env.decls.size := by
    apply mkOr_le_size
  omega

theorem lt_mkOr_size_of_lt_env_size (env : Env) (lhs rhs : Nat) (hl hr)
    (h : x < env.decls.size)
    : x < (env.mkOr lhs rhs hl hr).env.decls.size := by
  have := mkOr_le_size env lhs rhs hl hr
  omega

@[simp]
theorem denote_mkOr_lhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkOr lhs rhs hl hr).env, ⟨lhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨lhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkOr_IsPrefix_env

@[simp]
theorem denote_mkOr_rhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkOr lhs rhs hl hr).env, ⟨rhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨rhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkOr_IsPrefix_env

theorem mkXor_le_size (env : Env) (lhs rhs : Nat) (hl) (hr)
    : env.decls.size ≤ (env.mkXor lhs rhs hl hr).env.decls.size := by
  simp only [mkXor]
  apply le_mkGate_size_of_le_env_size
  apply le_mkGate_size_of_le_env_size
  apply le_mkGate_size_of_le_env_size
  omega

theorem mkXor_decl_eq idx (env : Env) (lhs rhs : Nat) {h : idx < env.decls.size}
    (hl) (hr) {h2} :
    (env.mkXor lhs rhs hl hr).env.decls[idx]'h2 = env.decls[idx] := by
  simp only [mkXor]
  rw [mkGate_decl_eq]
  rw [mkGate_decl_eq]
  rw [mkGate_decl_eq]

theorem mkXor_IsPrefix_env (env : Env) (lhs rhs : Nat) {hl} {hr} :
    IsPrefix env.decls (env.mkXor lhs rhs hl hr).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkXor_decl_eq
  . apply mkXor_le_size

@[simp]
theorem denote_mkXor :
    ⟦env.mkXor lhs rhs hl hr, assign⟧
      =
    xor ⟦env, ⟨lhs, hl⟩, assign⟧ ⟦env, ⟨rhs, hr⟩, assign⟧ := by
  rw [← xor_as_and]
  simp only [mkXor, denote_mkGate, denote_mkGate_entry, Bool.xor_false, Bool.xor_true,
    denote_projected_entry]
  rw [denote_mkGate_lhs ⟨env, lhs, hl⟩]
  rw [denote_mkGate_rhs ⟨env, rhs, hr⟩]

theorem lt_mkXor_size (entry : Entrypoint) (lhs hrs : Nat) (hl) (hr)
    : entry.start < (entry.env.mkXor lhs rhs hl hr).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkXor lhs rhs hl hr).env.decls.size := by
    apply mkXor_le_size
  omega

theorem lt_mkXor_size_of_lt_env_size (env : Env) (lhs rhs : Nat) (hl hr)
    (h : x < env.decls.size)
    : x < (env.mkXor lhs rhs hl hr).env.decls.size := by
  have := mkXor_le_size env lhs rhs hl hr
  omega

@[simp]
theorem denote_mkXor_lhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkXor lhs rhs hl hr).env, ⟨lhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨lhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkXor_IsPrefix_env

@[simp]
theorem denote_mkXor_rhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkXor lhs rhs hl hr).env, ⟨rhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨rhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkXor_IsPrefix_env

theorem mkBEq_le_size (env : Env) (lhs rhs : Nat) (hl) (hr)
    : env.decls.size ≤ (env.mkBEq lhs rhs hl hr).env.decls.size := by
  simp only [mkBEq]
  apply le_mkGate_size_of_le_env_size
  apply le_mkGate_size_of_le_env_size
  apply le_mkGate_size_of_le_env_size
  omega

theorem mkBEq_decl_eq idx (env : Env) (lhs rhs : Nat) {h : idx < env.decls.size}
    (hl) (hr) {h2} :
    (env.mkBEq lhs rhs hl hr).env.decls[idx]'h2 = env.decls[idx] := by
  simp only [mkBEq]
  rw [mkGate_decl_eq]
  rw [mkGate_decl_eq]
  rw [mkGate_decl_eq]

theorem mkBEq_IsPrefix_env (env : Env) (lhs rhs : Nat) {hl} {hr} :
    IsPrefix env.decls (env.mkBEq lhs rhs hl hr).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkBEq_decl_eq
  . apply mkBEq_le_size

@[simp]
theorem denote_mkBEq :
    ⟦env.mkBEq lhs rhs hl hr, assign⟧
      =
    (⟦env, ⟨lhs, hl⟩, assign⟧ == ⟦env, ⟨rhs, hr⟩, assign⟧) := by
  rw [← beq_as_and]
  simp only [mkBEq, denote_mkGate, denote_mkGate_entry, Bool.xor_false, Bool.xor_true,
    denote_projected_entry]
  rw [denote_mkGate_lhs ⟨env, lhs, hl⟩]
  rw [denote_mkGate_rhs ⟨env, rhs, hr⟩]

theorem lt_mkBEq_size (entry : Entrypoint) (lhs hrs : Nat) (hl) (hr)
    : entry.start < (entry.env.mkBEq lhs rhs hl hr).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkBEq lhs rhs hl hr).env.decls.size := by
    apply mkBEq_le_size
  omega

theorem lt_mkBEq_size_of_lt_env_size (env : Env) (lhs rhs : Nat) (hl hr)
    (h : x < env.decls.size)
    : x < (env.mkBEq lhs rhs hl hr).env.decls.size := by
  have := mkBEq_le_size env lhs rhs hl hr
  omega

@[simp]
theorem denote_mkBEq_lhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkBEq lhs rhs hl hr).env, ⟨lhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨lhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkBEq_IsPrefix_env

@[simp]
theorem denote_mkBEq_rhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkBEq lhs rhs hl hr).env, ⟨rhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨rhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkBEq_IsPrefix_env

theorem mkImp_le_size (env : Env) (lhs rhs : Nat) (hl) (hr)
    : env.decls.size ≤ (env.mkImp lhs rhs hl hr).env.decls.size := by
  simp only [mkImp]
  apply le_mkGate_size_of_le_env_size
  apply le_mkConst_size_of_le_env_size
  apply le_mkGate_size_of_le_env_size
  omega

theorem mkImp_decl_eq idx (env : Env) (lhs rhs : Nat) {h : idx < env.decls.size}
    (hl) (hr) {h2} :
    (env.mkImp lhs rhs hl hr).env.decls[idx]'h2 = env.decls[idx] := by
  simp only [mkImp]
  rw [mkGate_decl_eq]
  rw [mkConst_decl_eq]
  rw [mkGate_decl_eq]
  apply lt_mkConst_size_of_lt_env_size
  apply lt_mkGate_size_of_lt_env_size
  assumption

theorem mkImp_IsPrefix_env (env : Env) (lhs rhs : Nat) {hl} {hr} :
    IsPrefix env.decls (env.mkImp lhs rhs hl hr).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply mkImp_decl_eq
  . apply mkImp_le_size

@[simp]
theorem denote_mkImp :
    ⟦env.mkImp lhs rhs hl hr, assign⟧
      =
    (!⟦env, ⟨lhs, hl⟩, assign⟧ || ⟦env, ⟨rhs, hr⟩, assign⟧) := by
  rw [← imp_as_and]
  simp [mkImp]
  
theorem lt_mkImp_size (entry : Entrypoint) (lhs hrs : Nat) (hl) (hr)
    : entry.start < (entry.env.mkImp lhs rhs hl hr).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (entry.env.mkImp lhs rhs hl hr).env.decls.size := by
    apply mkImp_le_size
  omega

theorem lt_mkImp_size_of_lt_env_size (env : Env) (lhs rhs : Nat) (hl hr)
    (h : x < env.decls.size)
    : x < (env.mkImp lhs rhs hl hr).env.decls.size := by
  have := mkImp_le_size env lhs rhs hl hr
  omega

@[simp]
theorem denote_mkImp_lhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkImp lhs rhs hl hr).env, ⟨lhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨lhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkImp_IsPrefix_env

@[simp]
theorem denote_mkImp_rhs (entry : Entrypoint) {hgate} {hl} {hr} {h} :
    ⟦(entry.env.mkImp lhs rhs hl hr).env, ⟨rhs, h⟩, assign⟧
      =
    ⟦entry.env, ⟨rhs, hgate⟩, assign⟧ :=  by
  apply denote.go_eq_of_env_eq
  apply mkImp_IsPrefix_env

end Env
