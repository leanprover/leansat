import LeanSAT.Reflect.Tactics.Reflect
import Std.Data.HashMap
open Std

-- Missing Array theorems?
theorem Array.push_get (as : Array α) (a : α) (h : i < (as.push a).size) : (as.push a)[i] = if _ : i < as.size then as[i] else a :=
  sorry

theorem Array.push_get_old (as : Array α) (a : α) (h : i < as.size) : (as.push a)[i]'(by simp; omega) = as[i] := by
  simp [Array.push_get, h]

theorem Array.push_get_size (as : Array α) (a : α) : (as.push a)[as.size] = a := by
  simp [Array.push_get]


inductive Decl where
| const (b : Bool)
| atom (idx : Nat)
| gate (x y : Nat) (xpol ypol : Bool)
deriving BEq, Hashable, Repr

inductive Cache.WF : Array Decl → HashMap Decl Nat → Prop where
| empty : Cache.WF decls HashMap.empty
| push_id (h : Cache.WF decls cache) : Cache.WF (decls.push decl) cache
| push_cache (h : Cache.WF decls cache) : Cache.WF (decls.push decl) (cache.insert decl decls.size)

def Cache (decls : Array Decl) := { map : HashMap Decl Nat // Cache.WF decls map }

def Cache.empty (decls : Array Decl) : Cache decl := ⟨HashMap.empty, WF.empty⟩

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
theorem IsDag.empty : IsDag #[] := by
  intro i lhs rhs lpol rpol h
  simp only [Array.size_toArray, List.length_nil] at h
  omega

structure Env where
  decls : Array Decl
  cache : Cache decls
  inv : IsDag decls

def Env.empty : Env := { decls := #[], cache := Cache.empty #[], inv := IsDag.empty }

structure Env.Entrypoint where
  env : Env
  start : Nat
  inv : start < env.decls.size

def Env.denote (entry : Env.Entrypoint) (assign : List Bool) : Bool :=
  go entry.start entry.env.decls assign entry.inv entry.env.inv
where
  go (x : Nat) (decls : Array Decl) (assign : List Bool) (h1 : x < decls.size) (h2 : IsDag decls) :=
    match h3 : decls[x] with
    | .const b => b
    | .atom v => assign.getD v false
    | .gate lhs rhs lpol rpol =>
      have := h2 x _ _ _ _ h1 h3
      let lval := go lhs decls assign (by omega) h2
      let rval := go rhs decls assign (by omega) h2
      xor lval lpol && xor rval rpol

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
  . next lhs1 rhs1 lpol1 rpol1 heq1 =>
    split
    . next heq2 => rw [h4, heq1] at heq2; injections
    . next heq2 => rw [h4, heq1] at heq2; injections
    . next lhs2 rhs2 lpol2 rpol2 heq2 =>
      rw [heq1, heq2] at h4
      injection h4 with lhseq rhseq lpoleq rpoleq
      simp only [lhseq, lpoleq, rhseq, rpoleq]
      have := inv x lhs1 rhs1 lpol1 rpol1 h1 heq1
      apply ReflectSat.EvalAtAtoms.and_congr
      all_goals
        apply ReflectSat.EvalAtAtoms.xor_congr
        . apply denote.go_lt_push
          assumption
        . rfl

def Env.mkGate (lhs rhs : Nat) (lpol rpol : Bool) (env : Env) (hl : lhs < env.decls.size) 
    (hr : rhs < env.decls.size) : Env.Entrypoint :=
  let g := env.decls.size
  let decls := env.decls.push (.gate lhs rhs lpol rpol)
  let cache := env.cache.noUpdate
  have inv := by
    intro i lhs rhs lpol rpol h1 h2
    simp only [decls, Array.push_get] at h2
    split at h2
    . apply env.inv <;> assumption
    . injections; omega
  ⟨{ env with decls, inv, cache }, g, by simp [g, decls]⟩

theorem Env.mkGate_le_size (lhs rhs : Nat) (lpol rpol : Bool) (env : Env) hl hr
    : env.decls.size ≤ (env.mkGate lhs rhs lpol rpol hl hr).env.decls.size := by
  simp_arith [mkGate]

theorem Env.lt_mkGate_size (e1 : Env.Entrypoint) (lhs rhs : Nat) (lpol rpol : Bool) hl hr
    : e1.start < (e1.env.mkGate lhs rhs lpol rpol hl hr).env.decls.size := by
  have h1 := e1.inv
  have h2 : e1.env.decls.size ≤ (e1.env.mkGate lhs rhs lpol rpol hl hr).env.decls.size :=
    Env.mkGate_le_size _ _ _ _ _ _ _
  omega

def Env.mkGateCached (lhs rhs : Nat) (lpol rpol : Bool) (env : Env) (hl : lhs < env.decls.size)
    (hr : rhs < env.decls.size) : Env.Entrypoint :=
  let decl := .gate lhs rhs lpol rpol
  match h:env.cache.find? decl with
  | some gate =>
    ⟨env, gate, by apply Cache.find?_bounds _ _ h⟩
  | none =>
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
    ⟨{ env with decls, inv, cache }, g, by simp [g, decls]⟩

theorem Env.mkGateCached_eval_eq_mkGate_eval (lhs rhs : Nat) (lpol rpol : Bool) (env : Env) (hl : lhs < env.decls.size)
    (hr : rhs < env.decls.size) : denote (env.mkGateCached lhs rhs lpol rpol hl hr) assign = denote (env.mkGate lhs rhs lpol rpol hl hr) assign := by
  simp only [mkGate, mkGateCached]
  split
  . next heq1 =>
    unfold denote denote.go
    have h1 := Cache.find?_property env.cache (.gate lhs rhs lpol rpol) heq1
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
        injection heq3 with lhseq rhseq lpoleq rpoleq
        simp only [lhseq, lpoleq, rhseq, rpoleq]
        simp_all only [Decl.gate.injEq]
        apply ReflectSat.EvalAtAtoms.and_congr
        all_goals
          apply ReflectSat.EvalAtAtoms.xor_congr
          . rw [denote.go_lt_push]
            exact env.inv
          . rfl
  . simp [denote]

def Env.mkAtom (n : Nat) (env : Env) : Env.Entrypoint :=
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
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

theorem Env.mkAtom_le_size (env : Env) (var : Nat)
    : env.decls.size ≤ (env.mkAtom var).env.decls.size := by
  simp_arith [mkAtom]

def Env.mkAtomCached (n : Nat) (env : Env) : Env.Entrypoint :=
  let decl := .atom n
  match h:env.cache.find? decl with
  | some gate =>
    ⟨env, gate, by apply Cache.find?_bounds _ _ h⟩
  | none =>
    let g := env.decls.size
    let decls := env.decls.push decl
    let cache := env.cache.insert decl
    have inv := by
      intro i lhs rhs lpol rpol h1 h2
      simp only [decls] at *
      simp only [Array.push_get] at h2
      split at h2
      . apply env.inv <;> assumption
      . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

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

def Env.mkConst (val : Bool) (env : Env) : Env.Entrypoint :=
  let g := env.decls.size
  let decls := env.decls.push (.const val)
  let cache := env.cache.noUpdate
  have inv := by
    intro i lhs rhs lpol rpol h1 h2
    simp only [decls] at *
    simp only [Array.push_get] at h2
    split at h2
    . apply env.inv <;> assumption
    . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

theorem Env.mkConst_le_size (env : Env) (val : Bool)
    : env.decls.size ≤ (env.mkConst val).env.decls.size := by
  simp_arith [mkConst]

theorem Env.lt_mkConst_size (e1 : Env.Entrypoint) : e1.start < (e1.env.mkConst val).env.decls.size := by
  have h1 := e1.inv
  have h2 : e1.env.decls.size ≤ (e1.env.mkConst val).env.decls.size :=
    Env.mkConst_le_size _ _
  omega

def Env.mkConstCached (val : Bool) (env : Env) : Env.Entrypoint :=
  let decl := .const val
  match h:env.cache.find? decl with
  | some gate =>
    ⟨env, gate, by apply Cache.find?_bounds _ _ h⟩
  | none =>
    let g := env.decls.size
    let decls := env.decls.push decl
    let cache := env.cache.insert decl
    have inv := by
      intro i lhs rhs lpol rpol h1 h2
      simp only [decls] at *
      simp only [Array.push_get] at h2
      split at h2
      . apply env.inv <;> assumption
      . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

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

-- TODO: implement version of this with cached functions and prove equivalent
def Env.ofBoolExprNat (expr : BoolExprNat) : Env.Entrypoint :=
  go expr Env.empty
where
  go (expr : BoolExprNat) (env : Env) : { entry : Env.Entrypoint // env.decls.size ≤ entry.env.decls.size } :=
    match expr with
    | .literal var => ⟨env.mkAtom var, (by apply Env.mkAtom_le_size)⟩
    | .const val => ⟨env.mkConst val, (by apply Env.mkConst_le_size)⟩
    | .not expr =>
      -- ¬x = true && invert x
      let ⟨exprEntry, _⟩ := go expr env
      let constEntry := exprEntry.env.mkConst true
      have := exprEntry.env.mkConst_le_size true
      let ret :=
       constEntry.env.mkGate
         constEntry.start
         exprEntry.start
         true
         false
         constEntry.inv
         (by apply Env.lt_mkConst_size)
      have := constEntry.env.mkGate_le_size _ _ true false constEntry.inv (by apply Env.lt_mkConst_size)
      ⟨ret, by dsimp [constEntry, ret] at *; omega⟩
    | .gate g lhs rhs =>
      let ⟨lhsEntry, _⟩ := go lhs env
      let ⟨rhsEntry, _⟩ := go rhs lhsEntry.env
      have h1 : lhsEntry.start < Array.size rhsEntry.env.decls := by
        have := lhsEntry.inv
        omega
      match g with
      | .and =>
        let ret :=
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            true
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ true true h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .or =>
        -- x or y = true && (invert (invert x && invert y))
        let auxEntry :=
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start 
            false
            false
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ false false h1 rhsEntry.inv
        let constEntry := auxEntry.env.mkConst true
        have := auxEntry.env.mkConst_le_size true
        let ret :=
          constEntry.env.mkGate
            constEntry.start
            auxEntry.start
            true
            false
            constEntry.inv
            (by apply Env.lt_mkConst_size)
        have := constEntry.env.mkGate_le_size _ auxEntry.start true false constEntry.inv (by apply Env.lt_mkConst_size)
        ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩
      | .xor =>
        -- x xor y = (invert (invert (x && y))) && (invert ((invert x) && (invert y)))
        let aux1Entry :=
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            true
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ true true h1 rhsEntry.inv
        have h3 : lhsEntry.start < aux1Entry.env.decls.size := by
          dsimp [aux1Entry] at *
          omega
        let aux2Entry :=
          aux1Entry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            false
            false
            h3
            (by apply Env.lt_mkGate_size)
        have := aux1Entry.env.mkGate_le_size _ _ false false h3 (by apply Env.lt_mkGate_size)
        let ret :=
          aux2Entry.env.mkGate
            aux1Entry.start
            aux2Entry.start
            false
            false
            (by apply Env.lt_mkGate_size)
            aux2Entry.inv
        have := aux2Entry.env.mkGate_le_size aux1Entry.start _ false false (by apply Env.lt_mkGate_size) aux2Entry.inv
        ⟨ret, by simp (config := { zetaDelta := true}) only at *; omega⟩
      | .beq =>
        -- a == b = (invert (a && (invert b))) && (invert ((invert a) && b))
        let aux1Entry :=
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            true
            false
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ true false h1 rhsEntry.inv
        have h3 : lhsEntry.start < aux1Entry.env.decls.size := by
          dsimp [aux1Entry] at *
          omega
        let aux2Entry :=
          aux1Entry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            false
            true
            h3
            (by apply Env.lt_mkGate_size)
        have := aux1Entry.env.mkGate_le_size _ _ false true h3 (by apply Env.lt_mkGate_size)
        let ret :=
          aux2Entry.env.mkGate
            aux1Entry.start
            aux2Entry.start
            false
            false
            (by apply Env.lt_mkGate_size)
            aux2Entry.inv
        have := aux2Entry.env.mkGate_le_size aux1Entry.start _ false false (by apply Env.lt_mkGate_size) aux2Entry.inv
        ⟨ret, by simp (config := { zetaDelta := true}) only at *; omega⟩
      | .imp =>
        -- a -> b = true && (invert (a and (invert b)))
        let auxEntry :=
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start 
            true
            false
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ true false h1 rhsEntry.inv
        let constEntry := mkConst true auxEntry.env
        have := auxEntry.env.mkConst_le_size true
        let ret :=
          constEntry.env.mkGate
            constEntry.start
            auxEntry.start
            true
            false
            constEntry.inv
            (by apply Env.lt_mkConst_size)
        have := constEntry.env.mkGate_le_size _ auxEntry.start true false constEntry.inv (by apply Env.lt_mkConst_size)
        ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩


#eval Env.ofBoolExprNat (.gate .and (.gate .and (.literal 0) (.literal 0)) (.gate .and (.literal 0) (.literal 0))) |>.env.decls
