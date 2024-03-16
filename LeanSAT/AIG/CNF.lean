import LeanSAT.AIG.Basic
import LeanSAT.Reflect.CNF.Basic
import LeanSAT.Reflect.CNF.Relabel
import LeanSAT.Reflect.CNF.Relabel
import LeanSAT.Reflect.BoolExpr.Tseitin.Defs
import LeanSAT.Reflect.BoolExpr.Tseitin.Lemmas

abbrev CNFVar (env : Env) := Nat ⊕ (Fin env.decls.size)

namespace Decl

def constToCNF (output : α) (const : Bool) : CNF α :=
  [[(output, const)]]

def gateToCNF (output : α) (lhs rhs : α) (linv rinv : Bool) : CNF α :=
    -- a ↔ (b and c) as CNF: (¬a ∨ b) ∧ (¬a ∨ c) ∧ (a ∨ ¬b ∨ ¬c)
    -- a ↔ (b and ¬c) as CNF: (¬a ∨ b) ∧ (¬a ∨ ¬c) ∧ (a ∨ ¬b ∨ c)
    -- a ↔ (¬b and c) as CNF: (¬a ∨ ¬b) ∧ (¬a ∨ c) ∧ (a ∨ b ∨ ¬c)
    -- a ↔ (¬b and ¬c) as CNF: (¬a ∨ ¬b) ∧ (¬a ∨ ¬c) ∧ (a ∨ b ∨ c)
   [
     [(output, false), (lhs, !linv)],
     [(output, false), (rhs, !rinv)],
     [(output, true),  (lhs, linv), (rhs, rinv)]
   ]

@[simp]
theorem constToCNF_eval :
    (constToCNF output b).eval assign
      =
    (assign output == b) := by
  simp [constToCNF, CNF.eval, CNF.Clause.eval]

theorem constToCNF_sat :
    (constToCNF output b).sat assign
      ↔
    (assign output = b) := by
  simp [CNF.sat]

@[simp]
theorem gateToCNF_eval :
    (gateToCNF output lhs rhs linv rinv).eval assign
      =
    (assign output == ((xor (assign lhs) linv) && (xor (assign rhs) rinv))) := by
  simp [gateToCNF, CNF.eval, CNF.Clause.eval]
  cases assign output
    <;> cases assign lhs
      <;> cases assign rhs
        <;> cases linv
          <;> cases rinv
            <;> decide

theorem gateToCNF_sat :
    (gateToCNF output lhs rhs linv rinv).sat assign
      ↔
    (assign output = ((xor (assign lhs) linv) && (xor (assign rhs) rinv))) := by
  simp [CNF.sat]

end Decl

namespace Env

-- TODO: cache
def toCNF (entry : Entrypoint) : CNF Nat :=
  let baseCnf := go entry.env entry.start entry.inv []
  let cnf : CNF (CNFVar entry.env) := [(.inr ⟨entry.start, entry.inv⟩, true)] :: baseCnf
  cnf.relabel inj
where
  inj {env : Env} (var : CNFVar env) : Nat :=
    match var with
    | .inl var => env.decls.size + var
    | .inr var => var.val
  go (env : Env) (upper : Nat) (h : upper < env.decls.size) (cnf : CNF (CNFVar env)) : CNF (CNFVar env) :=
    let decl := env.decls[upper]
    let output := .inr ⟨upper, h⟩
    match heq:decl with
    | .const b => Decl.constToCNF output b ++ cnf
    | .atom a => CNF.eq output (.inl a) ++ cnf
    | .gate lhs rhs linv rinv =>
      have := env.inv upper lhs rhs linv rinv h heq
      let lCNF := go env lhs (by omega) cnf
      let rCNF := go env rhs (by omega) lCNF
      Decl.gateToCNF output (.inr ⟨lhs, (by omega)⟩) (.inr ⟨rhs, (by omega)⟩) linv rinv ++ rCNF

theorem toCNF.inj_is_injection {env : Env} (a b : CNFVar env) :
    toCNF.inj a = toCNF.inj b → a = b := by
  intro h
  cases a with
  | inl =>
    cases b with
    | inl =>
      dsimp [inj] at h
      apply congrArg
      apply Nat.add_left_cancel
      exact h
    | inr rhs =>
      exfalso
      dsimp [inj] at h
      have := rhs.isLt
      omega
  | inr lhs =>
    cases b with
    | inl =>
      exfalso
      dsimp [inj] at h
      have := lhs.isLt
      omega
    | inr =>
      dsimp [inj] at h
      apply congrArg
      apply Fin.eq_of_val_eq
      exact h

-- TODO: simplify and move to basic theory
theorem denote_idx_const (h : env.decls[start] = .const b) :
    ⟦env, ⟨start, hstart⟩, assign⟧ = b := by
  unfold denote denote.go
  split <;> simp_all

theorem denote_idx_atom (h : env.decls[start] = .atom a) :
    ⟦env, ⟨start, hstart⟩, assign⟧ = assign a := by
  unfold denote denote.go
  split <;> simp_all

theorem denote_idx_gate (h : env.decls[start] = .gate lhs rhs linv rinv) :
    ⟦env, ⟨start, hstart⟩, assign⟧
      =
    (
      (xor ⟦env, ⟨lhs, by have := env.inv start lhs rhs linv rinv hstart h; omega⟩, assign⟧ linv)
        &&
      (xor ⟦env, ⟨rhs, by have := env.inv start lhs rhs linv rinv hstart h; omega⟩, assign⟧ rinv)
    ) := by
  unfold denote
  conv =>
    lhs
    unfold denote.go
  split
  . simp_all
  . simp_all
  . next heq =>
    rw [h] at heq
    simp_all

theorem toCNF.go_commute (env : Env) (base) (rhs lhs) (hl) (hr) (assign) :
    (go env rhs hr (go env lhs hl base)).eval assign
      =
    (go env lhs hl (go env rhs hr base)).eval assign := by
  sorry

theorem toCNF.denote_as_go (env : Env) (upper : Nat) (h1) (assign) (base) :
    ((assign (.inr ⟨upper, h1⟩) == ⟦env, ⟨upper, h1⟩, (fun var => assign (.inl var))⟧) = false)
      →
    ((go env upper h1 base).eval assign = false) := by
  intro h
  unfold go
  dsimp
  split
  . next b heq =>
    rw [denote_idx_const heq] at h
    simp [h]
  . next a heq =>
    rw [denote_idx_atom heq] at h
    simp [h]
  . next lhs rhs linv rinv heq =>
    rw [denote_idx_gate heq] at h
    simp
    have := env.inv upper lhs rhs linv rinv h1 heq
    match hl:(assign (.inr ⟨lhs, by omega⟩) == ⟦env, ⟨lhs, by omega⟩, fun var => assign (Sum.inl var)⟧) with
    | true =>
      match hr:(assign (.inr ⟨rhs, by omega⟩) == ⟦env, ⟨rhs, by omega⟩, fun var => assign (Sum.inl var)⟧) with
      | true =>
        simp at hl hr
        rw [← hl, ← hr] at h
        simp [h]
      | false =>
        have rih := toCNF.denote_as_go env rhs (by omega) assign (go env lhs (by omega) base) hr
        simp [rih]
    | false =>
      have lih := toCNF.denote_as_go env lhs (by omega) assign (go env rhs (by omega) base) hl
      rw [go_commute]
      simp [lih]

def mixAssigns {env : Env} (assign1 : Nat → Bool) (assign2 : Fin env.decls.size → Bool)
    : CNFVar env → Bool
  | .inl var => assign1 var
  | .inr var => assign2 var

-- TODO: simp theorems
def toCNF.satAssignment (env : Env) (assign1 : Nat → Bool) : CNFVar env → Bool :=
  mixAssigns assign1 (fun idx => ⟦env, ⟨idx.val, idx.isLt⟩, assign1⟧)

theorem toCNF.go_sat (env : Env) (start : Nat) (h1 : start < env.decls.size) (assign1 : Nat → Bool)
    (base : CNF (CNFVar env)) (hbase : base.sat (satAssignment env assign1)):
    (go env start h1 base).sat (satAssignment env assign1) := by
  unfold CNF.sat
  unfold go
  dsimp
  split
  . next b heq =>
    simp [satAssignment, mixAssigns]
    rw [denote_idx_const heq]
    simpa using hbase
  . next b heq =>
    simp [satAssignment, mixAssigns]
    rw [denote_idx_atom heq]
    simpa using hbase
  . next lhs rhs linv rinv heq =>
    simp [satAssignment, mixAssigns]
    rw [denote_idx_gate heq]
    have := env.inv start lhs rhs linv rinv h1 heq
    have lih := go_sat env lhs (by omega) assign1 base hbase
    have rih := go_sat env rhs (by omega) assign1 (go env lhs (by omega) base) lih
    simpa using rih

theorem toCNF.go_as_denote (env : Env) (start) (h1) (assign1) :
    ((⟦env, ⟨start, h1⟩, assign1⟧ && (go env start h1 []).eval (satAssignment env assign1)) = false)
      →
    (⟦env, ⟨start, h1⟩, assign1⟧ = false) := by
  intro h
  rw [go_sat env start h1 assign1 [] (by simp)] at h
  simpa using h

theorem toCNF_equisat (entry : Entrypoint) : entry.unsat ↔ (toCNF entry).unsat := by
  dsimp [toCNF]
  rw [CNF.unsat_relabel_iff]
  . constructor
    . simp [CNF.unsat, CNF.eval_succ, Entrypoint.unsat]
      intro h assign
      specialize h (fun var => assign (.inl var))
      match h2:assign (.inr ⟨entry.start, entry.inv⟩) with
      | true =>
        simp
        apply toCNF.denote_as_go
        rw [h]
        simp [h2]
      | false => simp
    . intro h assign1
      specialize h (toCNF.satAssignment entry.env assign1)
      apply toCNF.go_as_denote
      simpa using h
  . intro a b _ _ hinj
    apply toCNF.inj_is_injection
    assumption

end Env
