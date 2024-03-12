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

theorem or_as_and (a b : Bool) : (!(!a && !b)) = (a || b) := by cases a <;> cases b <;> decide
theorem xor_as_and (a b : Bool) : (!(a && b) && !(!a && !b)) = (xor a b) := by cases a <;> cases b <;> decide
theorem beq_as_and (a b : Bool) : (!(a && !b) && !(!a && b)) = (a == b) := by cases a <;> cases b <;> decide
theorem imp_as_and (a b : Bool) : (!(a && !b)) = (!a || b) := by cases a <;> cases b <;> decide

/--
A circuit node declaration. These are not recursive but instead contain indices into an `Env`.
-/
inductive Decl where
  /--
  A node with a constant output value.
  -/
  | const (b : Bool)
  /--
  An input node to the circuit.
  -/
  | atom (idx : Nat)
  /--
  An AIG gate with configurable input nodes and polarity. `l` and `r` are the
  input node indices while `linv` and `rinv` say whether there is an inverter on
  the left or right input.
  -/
  | gate (l r : Nat) (linv rinv : Bool)
  deriving BEq, Hashable, Repr

/--
A `Cache` is valid with respect to a list of declarations iff:
Whenever `cache.find? decl` returns an index into `xs : Array Decl`, `xs[index] = decl`.
This predicate limits a `HashMap Decl Nat` to this behavior.
-/
inductive Cache.WF : Array Decl → HashMap Decl Nat → Prop where
  /--
  An empty `Cache` is valid for any `Array Decl` as it never has a hit.
  -/
  | empty : Cache.WF decls HashMap.empty
  /--
  Given a `cache`, valid with respect to some `decls`, we can extend the `decls` without
  extending the cache and remain valid.
  -/
  | push_id (h : Cache.WF decls cache) : Cache.WF (decls.push decl) cache
  /--
  Given a `cache`, valid with respect to some `decls`, we can extend the `decls`
  and the `cache` at the same time with the same values and remaind valid.
  -/
  | push_cache (h : Cache.WF decls cache) : Cache.WF (decls.push decl) (cache.insert decl decls.size)

/--
A cache that is valid with respect to some `Array Decl`.
-/
def Cache (decls : Array Decl) := { map : HashMap Decl Nat // Cache.WF decls map }

/--
Create an empty `Cache`, valid with respect to any `Array Decl`.
-/
def Cache.empty (decls : Array Decl) : Cache decl := ⟨HashMap.empty, WF.empty⟩

@[inherit_doc Cache.WF.push_id]
def Cache.noUpdate (cache : Cache decls) : Cache (decls.push decl) :=
  ⟨cache.val, Cache.WF.push_id cache.property⟩

@[inherit_doc Cache.WF.push_cache]
def Cache.insert (cache : Cache decls) (decl : Decl) : Cache (decls.push decl) :=
  ⟨cache.val.insert decl decls.size, Cache.WF.push_cache cache.property⟩

/--
Lookup a `decl` in a `cache`.

If this returns `some i`, `Cache.find?_poperty` can be used to demonstrate: `decls[i] = decl`.
-/
def Cache.find? (cache : Cache decls) (decl : Decl) : Option Nat :=
  cache.val.find? decl

/--
This axiom states that all indices, found in a `Cache` that is valid with respect to some `decls`,
are within bounds of `decls`.
-/
axiom Cache.find?_bounds {decls : Array Decl} {idx : Nat} (c : Cache decls) (decl : Decl)
    (h : c.find? decl = some idx) : idx < decls.size

/--
This axiom states that if `Cache.find? decl` returns `some i`, `decls[i] = decl`, holds.
-/
axiom Cache.find?_property {decls : Array Decl} {idx : Nat} (c : Cache decls) (decl : Decl)
    (h : c.find? decl = some idx) : decls[idx]'(Cache.find?_bounds c decl h) = decl

/--
An `Array Decl` is a Direct Acyclic Graph (DAG) if this holds.
-/
def IsDag (decls : Array Decl) : Prop := ∀ i lhs rhs linv rinv (h : i < decls.size), decls[i] = .gate lhs rhs linv rinv → lhs < i ∧ rhs < i

/--
The empty array is a DAG.
-/
theorem IsDag.empty : IsDag #[] := by
  intro i lhs rhs linv rinv h
  simp only [Array.size_toArray, List.length_nil] at h
  omega

/--
An And Inverter Graph (AIG) together with a cache for subterm sharing.
-/
structure Env where
  /--
  The circuit itself as an `Array Decl` whose members have indices into said array.
  -/
  decls : Array Decl
  /--
  The `Decl` cache, valid with respect to `decls`.
  -/
  cache : Cache decls
  /--
  In order to be a valid AIG, `decls` must form a DAG.
  -/
  inv : IsDag decls

/--
An `Env` with an empty AIG and cache.
-/
def Env.empty : Env := { decls := #[], cache := Cache.empty #[], inv := IsDag.empty }

/--
An entrypoint into an `Env`. This can be used to evaluate a circuit, starting at a certain node,
with `Env.denote` or to construct bigger circuits
-/
structure Env.Entrypoint where
  /--
  The AIG that we are in.
  -/
  env : Env
  /--
  The AIG node at which to begin evaluation.
  -/
  start : Nat
  /--
  The AIG node must be within bounds.
  -/
  inv : start < env.decls.size

/--
Evaluate an `Env.Entrypoint` using some assignment for atoms.
-/
def Env.denote (entry : Env.Entrypoint) (assign : List Bool) : Bool :=
  go entry.start entry.env.decls assign entry.inv entry.env.inv
where
  go (x : Nat) (decls : Array Decl) (assign : List Bool) (h1 : x < decls.size) (h2 : IsDag decls) :=
    match h3 : decls[x] with
    | .const b => b
    | .atom v => assign.getD v false
    | .gate lhs rhs linv rinv =>
      have := h2 x _ _ _ _ h1 h3
      let lval := go lhs decls assign (by omega) h2
      let rval := go rhs decls assign (by omega) h2
      xor lval linv && xor rval rinv

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
Build an AIG gate in `env`. Note that his version is only meant for proving,
for production purposes use `Env.mkGateCached` and equality theorems to this one.
-/
def Env.mkGate (lhs rhs : Nat) (linv rinv : Bool) (env : Env) (hl : lhs < env.decls.size)
    (hr : rhs < env.decls.size) : Env.Entrypoint :=
  let g := env.decls.size
  let decls := env.decls.push (.gate lhs rhs linv rinv)
  let cache := env.cache.noUpdate
  have inv := by
    intro i lhs rhs linv rinv h1 h2
    simp only [decls, Array.push_get] at h2
    split at h2
    . apply env.inv <;> assumption
    . injections; omega
  ⟨{ env with decls, inv, cache }, g, by simp [g, decls]⟩


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
A version of `Env.mkGate` that uses the subterm cache in `Env`. This version is meant for
programmming, for proving purposes use `Env.mkGate` and equality theorems to this one.
-/
def Env.mkGateCached (lhs rhs : Nat) (linv rinv : Bool) (env : Env) (hl : lhs < env.decls.size)
    (hr : rhs < env.decls.size) : Env.Entrypoint :=
  let decl := .gate lhs rhs linv rinv
  match h:env.cache.find? decl with
  | some gate =>
    ⟨env, gate, by apply Cache.find?_bounds _ _ h⟩
  | none =>
    let g := env.decls.size
    let decls := env.decls.push decl
    let cache := Cache.insert env.cache decl
    have inv := by
      intro lhs rhs linv rinv i h1 h2
      simp only [decls] at *
      simp only [Array.push_get] at h2
      split at h2
      . apply env.inv <;> assumption
      . injections; omega
    ⟨{ env with decls, inv, cache }, g, by simp [g, decls]⟩

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
Add a new input node to the AIG in `env`. Note that his version is only meant for proving,
for production purposes use `Env.mkAtomCached` and equality theorems to this one.
-/
def Env.mkAtom (n : Nat) (env : Env) : Env.Entrypoint :=
  let g := env.decls.size
  let decls := env.decls.push (.atom n)
  let cache := env.cache.noUpdate
  have inv := by
    intro i lhs rhs linv rinv h1 h2
    simp only [decls] at *
    simp only [Array.push_get] at h2
    split at h2
    . apply env.inv <;> assumption
    . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

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

/--
A version of `Env.mkAtom` that uses the subterm cache in `Env`. This version is meant for
programmming, for proving purposes use `Env.mkAtom` and equality theorems to this one.
-/
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
      intro i lhs rhs linv rinv h1 h2
      simp only [decls] at *
      simp only [Array.push_get] at h2
      split at h2
      . apply env.inv <;> assumption
      . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

/--
`Env.mkAtomCached` never shrinks the underlying AIG.
-/
theorem Env.mkAtomCached_le_size (env : Env) (var : Nat)
    : env.decls.size ≤ (env.mkAtomCached var).env.decls.size := by
  dsimp [mkAtomCached]
  split
  . simp
  . simp_arith

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
Build an constant node in `env`. Note that his version is only meant for proving,
for production purposes use `Env.mkConstCached` and equality theorems to this one.
-/
def Env.mkConst (val : Bool) (env : Env) : Env.Entrypoint :=
  let g := env.decls.size
  let decls := env.decls.push (.const val)
  let cache := env.cache.noUpdate
  have inv := by
    intro i lhs rhs linv rinv h1 h2
    simp only [decls] at *
    simp only [Array.push_get] at h2
    split at h2
    . apply env.inv <;> assumption
    . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

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

/--
A version of `Env.mkConst` that uses the subterm cache in `Env`. This version is meant for
programmming, for proving purposes use `Env.mkGate` and equality theorems to this one.
-/
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
      intro i lhs rhs linv rinv h1 h2
      simp only [decls] at *
      simp only [Array.push_get] at h2
      split at h2
      . apply env.inv <;> assumption
      . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

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

/--
Turn a `BoolExprNat` into an AIG + entrypoint. Note that this version is only meant
for proving purposes. For programming use `Env.ofBoolExprNatCached` and equality theorems.
-/
def Env.ofBoolExprNat (expr : BoolExprNat) : Env.Entrypoint :=
  go expr Env.empty |>.val
where
  /--
  This function contains a series of `have` statements that fulfill no obvious purpose.
  They are used to prove the `env.decls.size ≤ entry.env.decls.size` invariant of the return
  value with the final omega call in each case. This invariant is necessary as we recursively
  call this function multiple times so we need to guarantee that no recursive call ever shrinks
  the AIG in order to be allowed to use the generated AIG nodes.
  -/
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
         false
         true
         constEntry.inv
         (by apply Env.lt_mkConst_size)
      have := constEntry.env.mkGate_le_size _ _ false true constEntry.inv (by apply Env.lt_mkConst_size)
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
            false
            false
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ false false h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .or =>
        -- x or y = true && (invert (invert x && invert y))
        let auxEntry :=
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            true
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ true true h1 rhsEntry.inv
        let constEntry := auxEntry.env.mkConst true
        have := auxEntry.env.mkConst_le_size true
        let ret :=
          constEntry.env.mkGate
            constEntry.start
            auxEntry.start
            false
            true
            constEntry.inv
            (by apply Env.lt_mkConst_size)
        have := constEntry.env.mkGate_le_size _ auxEntry.start false true constEntry.inv (by apply Env.lt_mkConst_size)
        ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩
      | .xor =>
        -- x xor y = (invert (invert (x && y))) && (invert ((invert x) && (invert y)))
        let aux1Entry :=
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            false
            false
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ false false h1 rhsEntry.inv
        have h3 : lhsEntry.start < aux1Entry.env.decls.size := by
          dsimp [aux1Entry] at *
          omega
        let aux2Entry :=
          aux1Entry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            true
            true
            h3
            (by apply Env.lt_mkGate_size)
        have := aux1Entry.env.mkGate_le_size _ _ true true h3 (by apply Env.lt_mkGate_size)
        let ret :=
          aux2Entry.env.mkGate
            aux1Entry.start
            aux2Entry.start
            true
            true
            (by apply Env.lt_mkGate_size)
            aux2Entry.inv
        have := aux2Entry.env.mkGate_le_size aux1Entry.start _ true true (by apply Env.lt_mkGate_size) aux2Entry.inv
        ⟨ret, by simp (config := { zetaDelta := true}) only at *; omega⟩
      | .beq =>
        -- a == b = (invert (a && (invert b))) && (invert ((invert a) && b))
        let aux1Entry :=
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            false
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ false true h1 rhsEntry.inv
        have h3 : lhsEntry.start < aux1Entry.env.decls.size := by
          dsimp [aux1Entry] at *
          omega
        let aux2Entry :=
          aux1Entry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            true
            false
            h3
            (by apply Env.lt_mkGate_size)
        have := aux1Entry.env.mkGate_le_size _ _ true false h3 (by apply Env.lt_mkGate_size)
        let ret :=
          aux2Entry.env.mkGate
            aux1Entry.start
            aux2Entry.start
            true
            true
            (by apply Env.lt_mkGate_size)
            aux2Entry.inv
        have := aux2Entry.env.mkGate_le_size aux1Entry.start _ true true (by apply Env.lt_mkGate_size) aux2Entry.inv
        ⟨ret, by simp (config := { zetaDelta := true}) only at *; omega⟩
      | .imp =>
        -- a -> b = true && (invert (a and (invert b)))
        let auxEntry :=
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            false
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ false true h1 rhsEntry.inv
        let constEntry := mkConst true auxEntry.env
        have := auxEntry.env.mkConst_le_size true
        let ret :=
          constEntry.env.mkGate
            constEntry.start
            auxEntry.start
            false
            true
            constEntry.inv
            (by apply Env.lt_mkConst_size)
        have := constEntry.env.mkGate_le_size _ auxEntry.start false true constEntry.inv (by apply Env.lt_mkConst_size)
        ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩


#eval Env.ofBoolExprNat (.gate .and (.gate .and (.literal 0) (.literal 0)) (.gate .and (.literal 0) (.literal 0))) |>.env.decls

theorem Env.ofBoolExprNat.go_decls_size_le (expr : BoolExprNat) (env : Env) :
    env.decls.size ≤ (ofBoolExprNat.go expr env).val.env.decls.size := by
  exact (ofBoolExprNat.go expr env).property

theorem Env.ofBoolExprNat.go_decl_eq (idx) (env) (h : idx < env.decls.size) (hbounds) :
    (ofBoolExprNat.go expr env).val.env.decls[idx]'hbounds = env.decls[idx] := by
  induction expr generalizing env with
  | const =>
    simp only [go]
    apply Env.mkConst_decl_eq
  | literal =>
    simp only [go]
    apply Env.mkAtom_decl_eq
  | not expr ih =>
    simp only [go]
    have := go_decls_size_le expr env
    specialize ih env (by omega) (by omega)
    -- TODO: I think I want a more general theorem here
    simp [mkConst, mkAtom, mkGate, Array.push_get]
    split
    . split
      . assumption
      . omega
    . omega
  | gate g lhs rhs lih rih =>
    have := go_decls_size_le lhs env
    have := go_decls_size_le rhs (go lhs env).val.env
    specialize lih env (by omega) (by omega)
    specialize rih (go lhs env).val.env (by omega) (by omega)
    cases g with
    | and =>
      -- TODO: other use case for simp lemma
      simp only [go]
      simp [mkGate, mkAtom, Array.push_get]
      split
      . simp [rih, lih]
      . omega
    | or =>
      -- TODO: other use case for simp lemma
      simp only [go]
      simp [mkGate, mkAtom, mkConst, Array.push_get]
      split
      . split
        . split
          . simp [lih, rih]
          . omega
        . omega
      . omega
    | xor =>
      -- TODO: other use case for simp lemma
      simp only [go]
      simp [mkGate, mkAtom, Array.push_get]
      split
      . split
        . split
          . simp [lih, rih]
          . omega
        . omega
      . omega
    | beq =>
      -- TODO: other use case for simp lemma
      simp only [go]
      simp [mkGate, mkAtom, Array.push_get]
      split
      . split
        . split
          . simp [lih, rih]
          . omega
        . omega
      . omega
    | imp =>
      -- TODO: other use case for simp lemma
      simp only [go]
      simp [mkGate, mkAtom, mkConst, Array.push_get]
      split
      . split
        . split
          . simp [lih, rih]
          . omega
        . omega
      . omega

@[simp]
theorem Env.foo (entry : Entrypoint) {h}:
    denote ⟨(ofBoolExprNat.go expr entry.env).val.env, entry.start, h⟩ assign
      =
    denote entry assign := by
  apply Env.denote.eq_of_env_eq
  . intro idx h
    apply Env.ofBoolExprNat.go_decl_eq
  . apply Env.ofBoolExprNat.go_decls_size_le

/-
denote
  {
    env :=
      (mkGate (ofBoolExprNat.go lhs env).val.start (ofBoolExprNat.go rhs (ofBoolExprNat.go lhs env).val.env).val.start
          false false (ofBoolExprNat.go rhs (ofBoolExprNat.go lhs env).val.env).val.env ⋯ ⋯).env,
    start := (ofBoolExprNat.go lhs env).val.start,
    inv := ⋯
  }
-/

-- TODO: much of this requires theorems about ofBoolExprNat.go in the spirit of Env.denote_mkConst_lt
theorem Env.ofBoolExprNatgo_eval_eq_eval (expr : BoolExprNat) (env : Env) (assign : List Bool) :
    denote (Env.ofBoolExprNat.go expr env) assign = expr.eval assign := by
  induction expr generalizing env with
  | const => simp [ofBoolExprNat.go]
  | literal => simp [ofBoolExprNat.go]
  | not expr ih =>
    simp [ofBoolExprNat.go]
    rw [← ih]
  | gate g lhs rhs lih rih =>
    cases g with
    | and =>
      simp [ofBoolExprNat.go, Gate.eval, lih, rih]
    | or =>
      simp [ofBoolExprNat.go, Gate.eval]
      rw [← or_as_and]
      simp [lih, rih]
    | xor =>
      simp [ofBoolExprNat.go, Gate.eval]
      rw [← xor_as_and]
      apply ReflectSat.EvalAtAtoms.and_congr
      . apply ReflectSat.EvalAtAtoms.not_congr
        sorry
      . apply ReflectSat.EvalAtAtoms.not_congr
        apply ReflectSat.EvalAtAtoms.and_congr
        . apply ReflectSat.EvalAtAtoms.not_congr
          sorry
        . apply ReflectSat.EvalAtAtoms.not_congr
          sorry
    | beq =>
      simp [ofBoolExprNat.go, Gate.eval]
      rw [← beq_as_and]
      apply ReflectSat.EvalAtAtoms.and_congr
      . apply ReflectSat.EvalAtAtoms.not_congr
        sorry
      . apply ReflectSat.EvalAtAtoms.not_congr
        apply ReflectSat.EvalAtAtoms.and_congr
        . apply ReflectSat.EvalAtAtoms.not_congr
          sorry
        . sorry
    | imp =>
      simp [ofBoolExprNat.go, Gate.eval]
      rw [← imp_as_and]
      simp [lih, rih]

theorem Env.ofBoolExprNat_eval_eq_eval (expr : BoolExprNat) (assign : List Bool) :
    denote (Env.ofBoolExprNat expr) assign = expr.eval assign := by
  apply Env.ofBoolExprNatgo_eval_eq_eval

-- lines such as: ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩
-- are slow because of the high defeq degree
-- TODO: ask leo how to fix this stuff
set_option pp.oneline true in
set_option trace.profiler true in
/--
Turn a `BoolExprNat` into an AIG + entrypoint. Note that this version is meant for programming
purposes. For proving use `Env.ofBoolExprNat` and equality theorems.
-/
def Env.ofBoolExprNatCached (expr : BoolExprNat) : Env.Entrypoint :=
  go expr Env.empty |>.val
where
  @[inherit_doc Env.ofBoolExprNat.go]
  go (expr : BoolExprNat) (env : Env) : { entry : Env.Entrypoint // env.decls.size ≤ entry.env.decls.size } :=
    match expr with
    | .literal var => ⟨env.mkAtomCached var, (by apply Env.mkAtomCached_le_size)⟩
    | .const val => ⟨env.mkConstCached val, (by apply Env.mkConstCached_le_size)⟩
    | .not expr =>
      -- ¬x = true && invert x
      let ⟨exprEntry, _⟩ := go expr env
      let constEntry := exprEntry.env.mkConstCached true
      have := exprEntry.env.mkConstCached_le_size true
      let ret :=
       constEntry.env.mkGateCached
         constEntry.start
         exprEntry.start
         false
         true
         constEntry.inv
         (by apply Env.lt_mkConstCached_size)
      have := constEntry.env.mkGateCached_le_size _ _ false true constEntry.inv (by apply Env.lt_mkConstCached_size)
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
          rhsEntry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            false
            false
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGateCached_le_size _ _ false false h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .or =>
        -- x or y = true && (invert (invert x && invert y))
        let auxEntry :=
          rhsEntry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            true
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGateCached_le_size _ _ true true h1 rhsEntry.inv
        let constEntry := auxEntry.env.mkConstCached true
        have := auxEntry.env.mkConstCached_le_size true
        let ret :=
          constEntry.env.mkGateCached
            constEntry.start
            auxEntry.start
            false
            true
            constEntry.inv
            (by apply Env.lt_mkConstCached_size)
        have := constEntry.env.mkGateCached_le_size _ auxEntry.start false true constEntry.inv (by apply Env.lt_mkConstCached_size)
        ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩
      | .xor =>
        -- x xor y = (invert (invert (x && y))) && (invert ((invert x) && (invert y)))
        let aux1Entry :=
          rhsEntry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            false
            false
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGateCached_le_size _ _ false false h1 rhsEntry.inv
        have h3 : lhsEntry.start < aux1Entry.env.decls.size := by
          dsimp [aux1Entry] at *
          omega
        let aux2Entry :=
          aux1Entry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            true
            true
            h3
            (by apply Env.lt_mkGateCached_size)
        have := aux1Entry.env.mkGateCached_le_size _ _ true true h3 (by apply Env.lt_mkGateCached_size)
        let ret :=
          aux2Entry.env.mkGateCached
            aux1Entry.start
            aux2Entry.start
            true
            true
            (by apply Env.lt_mkGateCached_size)
            aux2Entry.inv
        have := aux2Entry.env.mkGateCached_le_size aux1Entry.start _ true true (by apply Env.lt_mkGateCached_size) aux2Entry.inv
        ⟨ret, by simp (config := { zetaDelta := true}) only at *; omega⟩
      | .beq =>
        -- a == b = (invert (a && (invert b))) && (invert ((invert a) && b))
        let aux1Entry :=
          rhsEntry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            false
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGateCached_le_size _ _ false true h1 rhsEntry.inv
        have h3 : lhsEntry.start < aux1Entry.env.decls.size := by
          dsimp [aux1Entry] at *
          omega
        let aux2Entry :=
          aux1Entry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            true
            false
            h3
            (by apply Env.lt_mkGateCached_size)
        have := aux1Entry.env.mkGateCached_le_size _ _ true false h3 (by apply Env.lt_mkGateCached_size)
        let ret :=
          aux2Entry.env.mkGateCached
            aux1Entry.start
            aux2Entry.start
            true
            true
            (by apply Env.lt_mkGateCached_size)
            aux2Entry.inv
        have := aux2Entry.env.mkGateCached_le_size aux1Entry.start _ true true (by apply Env.lt_mkGateCached_size) aux2Entry.inv
        ⟨ret, by simp (config := { zetaDelta := true}) only at *; omega⟩
      | .imp =>
        -- a -> b = true && (invert (a and (invert b)))
        let auxEntry :=
          rhsEntry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            false
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGateCached_le_size _ _ false true h1 rhsEntry.inv
        let constEntry := mkConstCached true auxEntry.env
        have := auxEntry.env.mkConstCached_le_size true
        let ret :=
          constEntry.env.mkGateCached
            constEntry.start
            auxEntry.start
            false
            true
            constEntry.inv
            (by apply Env.lt_mkConstCached_size)
        have := constEntry.env.mkGateCached_le_size _ auxEntry.start false true constEntry.inv (by apply Env.lt_mkConstCached_size)
        ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩

#eval Env.ofBoolExprNatCached (.gate .and (.gate .and (.literal 0) (.literal 0)) (.gate .and (.literal 0) (.literal 0))) |>.env.decls

theorem Env.ofBoolExprCachedgo_eval_eq_ofBoolExprgo_eval (expr : BoolExprNat) (assign : List Bool) (env : Env) :
    Env.denote (Env.ofBoolExprNatCached.go expr env).val assign = Env.denote (Env.ofBoolExprNat.go expr env).val assign := by
  sorry

theorem Env.ofBoolExprCached_eval_eq_ofBoolExpr_eval (expr : BoolExprNat) (assign : List Bool) :
    Env.denote (Env.ofBoolExprNatCached expr) assign = Env.denote (Env.ofBoolExprNat expr) assign := by
  unfold Env.ofBoolExprNatCached
  rw [Env.ofBoolExprCachedgo_eval_eq_ofBoolExprgo_eval]
  unfold Env.ofBoolExprNat
  rfl
