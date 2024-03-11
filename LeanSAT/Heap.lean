import LeanSAT.Reflect.Tactics.Reflect
import Std.Data.HashMap
open Std

inductive Decl where
| atom (idx : Nat)
| gate (x y : Nat) (xpol ypol : Bool)
deriving BEq, Hashable

inductive Cache.WF : Array Decl → HashMap Decl Nat → Prop where
| empty : Cache.WF decls HashMap.empty
| push_id (h : Cache.WF decls cache) : Cache.WF (decls.push decl) cache
| push_cache (h : Cache.WF decls cache) : Cache.WF (decls.push decl) (cache.insert decl decls.size)

def Cache (decls : Array Decl) := { map : HashMap Decl Nat // Cache.WF decls map }

def Cache.noUpdate (cache : Cache decls) : Cache (decls.push decl) :=
  ⟨cache.val, Cache.WF.push_id cache.property⟩

def Cache.insert (cache : Cache decls) (decl : Decl) : Cache (decls.push decl) :=
  ⟨cache.val.insert decl decls.size, Cache.WF.push_cache cache.property⟩

def Cache.find? (cache : Cache decls) (decl : Decl) : Option Nat :=
  cache.val.find? decl

-- TODO: This is probably provable by building a better cache API
axiom Cache.find?_bounds {decls : Array Decl} {idx : Nat} (c : Cache decls) (decl : Decl)
    (h : c.find? decl = some idx) : idx < decls.size

axiom Cache.find?_property {decls : Array Decl} {idx : Nat} (c : Cache decls) (decl : Decl)
    (h : c.find? decl = some idx) : decls[idx]'(Cache.find?_bounds c decl h) = decl

def IsDag (decls : Array Decl) : Prop := ∀ i lhs rhs lpol rpol (h : i < decls.size), decls[i] = .gate lhs rhs lpol rpol → lhs < i ∧ rhs < i

structure Env where
  decls : Array Decl
  cache : Cache decls
  inv : IsDag decls

def denote (x : Nat) (assign : List Bool) (env : Env) : Bool :=
  go x assign env.decls env.inv
where
  go (x : Nat) (assign : List Bool) (decls : Array Decl) (h : IsDag decls) :=
    if h₁ : x < decls.size then
      match h₂ : decls[x] with
      | .atom b  => assign.getD b false
      | .gate lhs rhs lpol rpol =>
        have := h x _ _ _ _ h₁ h₂
        let lval := go lhs assign decls h
        let rval := go rhs assign decls h
        xor lval lpol && xor rval rpol
    else
      true

-- Missing Array theorems?
theorem Array.push_get (as : Array α) (a : α) (h : i < (as.push a).size) : (as.push a)[i] = if _ : i < as.size then as[i] else a :=
  sorry

theorem Array.push_get_old (as : Array α) (a : α) (h : i < as.size) : (as.push a)[i]'(by simp; omega) = as[i] := by
  simp [Array.push_get, h]

theorem Array.push_get_size (as : Array α) (a : α) : (as.push a)[as.size] = a := by
  simp [Array.push_get]

theorem denote.go_lt_push (x : Nat) (decls : Array Decl) (h1 : x < decls.size) {h2} {h3} (inv : IsDag decls) :
    (denote.go x assign decls h2) = (denote.go x assign (decls.push decl) h3) := by
  have h4 : x < decls.size + 1 := by omega
  unfold denote.go
  simp [h1, h4]
  rw [Array.push_get_old]
  split
  . next heq1 =>
    rw [heq1]
  . next lhs rhs lpol rpol heq1 =>
    rw [heq1]
    simp
    have := inv x lhs rhs lpol rpol h1 heq1
    apply ReflectSat.EvalAtAtoms.and_congr
    all_goals
      apply ReflectSat.EvalAtAtoms.xor_congr
      . apply denote.go_lt_push
        omega
        assumption
      . rfl

def mkGate (lhs rhs : Nat) (lpol rpol : Bool) (env : Env) (hl : lhs < env.decls.size) (hr : rhs < env.decls.size) : Nat × Env :=
  let g := env.decls.size
  let decls := env.decls.push (.gate lhs rhs lpol rpol)
  let cache := env.cache.noUpdate
  have inv := by
    intro i lhs rhs lpol rpol h1 h2
    simp only [decls, Array.push_get] at h2
    split at h2
    . apply env.inv <;> assumption
    . injections; omega
  (g, { env with decls, inv, cache })

def mkGateCache (lhs rhs : Nat) (lpol rpol : Bool) (env : Env) (hl : lhs < env.decls.size) (hr : rhs < env.decls.size) : Nat × Env :=
  let decl := .gate lhs rhs lpol rpol
  if let some gate := env.cache.find? decl then
    (gate, env)
  else
    let g := env.decls.size
    let decls := env.decls.push decl
    let cache := Cache.insert env.cache decl
    have inv := by
      intro lhs rhs lpol rpol i h1 h2
      simp only [decls] at *
      simp only [Array.push_get] at h2
      split at h2
      . apply env.inv <;> assumption
      . injections; omega
    (g, { env with decls, inv, cache })

theorem mkGateCache_eval_eq_mkGate_eval (lhs rhs : Nat) (lpol rpol : Bool) (env : Env) (hl : lhs < env.decls.size)
    (hr : rhs < env.decls.size)
    : let (g1, e1) := mkGateCache lhs rhs lpol rpol env hl hr
      let (g2, e2) := mkGate lhs rhs lpol rpol env hl hr
      denote g1 assign e1 = denote g2 assign e2 := by
  simp only [mkGate, mkGateCache]
  split
  . next heq1 =>
    unfold denote denote.go
    have h1 := Cache.find?_bounds env.cache (.gate lhs rhs lpol rpol) heq1
    have h2 := Cache.find?_property env.cache (.gate lhs rhs lpol rpol) heq1
    simp only [h1, Array.size_push, Nat.lt_succ_self, ↓reduceDite]
    rw [Array.push_get_size]
    split
    . next heq2 => simp [h2] at heq2
    . simp_all
      apply ReflectSat.EvalAtAtoms.and_congr
      all_goals
        apply ReflectSat.EvalAtAtoms.xor_congr
        . rw [denote.go_lt_push]
          assumption
          exact env.inv
        . rfl
  . simp [denote]

theorem mkGate_lt : (mkGate lhs rhs lpol rpol env hx hy).1 < (mkGate lhs rhs lpol rpol env hx hy).2.decls.size := by
  simp [mkGate]

def mkAtom (n : Nat) (env : Env) : Nat × Env :=
  let g := env.decls.size
  let decls := env.decls.push (.atom n)
  let cache := env.cache.noUpdate
  have inv := by
    intro i lhs rhs lpol rpol h1 h2
    simp only [decls] at *
    simp only [Array.push_get] at h2
    split at h2
    . apply env.inv <;> assumption
    . contradiction
  (g, { decls, inv, cache })

def mkAtomCache (n : Nat) (env : Env) : Nat × Env :=
  let decl := .atom n
  if let some gate := env.cache.find? decl then
    (gate, env)
  else
    let g := env.decls.size
    let decls := env.decls.push (.atom n)
    let cache := env.cache.noUpdate
    have inv := by
      intro i lhs rhs lpol rpol h1 h2
      simp only [decls] at *
      simp only [Array.push_get] at h2
      split at h2
      . apply env.inv <;> assumption
      . contradiction
    (g, { decls, inv, cache })

theorem mkAtomCache_eval_eq_mkAtom_eval (var : Nat) (env : Env)
    : let (g1, e1) := mkAtomCache var env
      let (g2, e2) := mkAtom var env
      denote g1 assign e1 = denote g2 assign e2 := by
    simp only [mkAtom, mkAtomCache]
    split
    . next heq1 =>
      unfold denote denote.go
      have h1 := Cache.find?_bounds env.cache (.atom var) heq1
      have h2 := Cache.find?_property env.cache (.atom var) heq1
      simp only [h1, ↓reduceDite, Array.size_push, Nat.lt_succ_self]
      rw [Array.push_get_size]
      split
      . next heq2 =>
        rw [h2] at heq2
        injection heq2 with heq3
        rw [heq3]
      . next heq2 => 
        rw [h2] at heq2
        injection heq2
    . simp [denote]
