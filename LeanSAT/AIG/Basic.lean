import LeanSAT.Reflect.Tactics.Reflect
import Std.Data.HashMap
open Std

theorem Array.get_push_old (as : Array α) (a : α) (h : i < as.size) : (as.push a)[i]'(by simp; omega) = as[i] := by
  simp [Array.get_push, h]

theorem Array.get_push_size (as : Array α) (a : α) : (as.push a)[as.size] = a := by
  simp [Array.get_push]

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
@[irreducible]
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

namespace Env

/--
An `Env` with an empty AIG and cache.
-/
def empty : Env := { decls := #[], cache := Cache.empty #[], inv := IsDag.empty }

/--
An entrypoint into an `Env`. This can be used to evaluate a circuit, starting at a certain node,
with `Env.denote` or to construct bigger circuits
-/
structure Entrypoint where
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
def denote (entry : Entrypoint) (assign : List Bool) : Bool :=
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

scoped syntax "⟦" term ", " term "⟧" : term
scoped syntax "⟦" term ", " "⟨" term ", " term "⟩" ", " term "⟧" : term

macro_rules
| `(⟦$entry, $assign⟧) => `(denote $entry $assign)
| `(⟦$env, ⟨$start, $hbound⟩, $assign⟧) => `(denote (Entrypoint.mk $env $start $hbound) $assign)

@[app_unexpander Env.denote]
def unexpandDenote : Lean.PrettyPrinter.Unexpander
  | `($(_) {env := $env, start := $start, inv := $hbound} $assign) => `(⟦$env, ⟨$start, $hbound⟩, $assign⟧)
  | `($(_) $entry $assign) => `(⟦$entry, $assign⟧)
  | _ => throw ()

/--
Build an AIG gate in `env`. Note that his version is only meant for proving,
for production purposes use `Env.mkGateCached` and equality theorems to this one.
-/
def mkGate (lhs rhs : Nat) (linv rinv : Bool) (env : Env) (hl : lhs < env.decls.size)
    (hr : rhs < env.decls.size) : Entrypoint :=
  let g := env.decls.size
  let decls := env.decls.push (.gate lhs rhs linv rinv)
  let cache := env.cache.noUpdate
  have inv := by
    intro i lhs rhs linv rinv h1 h2
    simp only [decls, Array.get_push] at h2
    split at h2
    . apply env.inv <;> assumption
    . injections; omega
  ⟨{ env with decls, inv, cache }, g, by simp [g, decls]⟩

/--
Add a new input node to the AIG in `env`. Note that his version is only meant for proving,
for production purposes use `Env.mkAtomCached` and equality theorems to this one.
-/
def mkAtom (n : Nat) (env : Env) : Entrypoint :=
  let g := env.decls.size
  let decls := env.decls.push (.atom n)
  let cache := env.cache.noUpdate
  have inv := by
    intro i lhs rhs linv rinv h1 h2
    simp only [decls] at *
    simp only [Array.get_push] at h2
    split at h2
    . apply env.inv <;> assumption
    . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

/--
Build an constant node in `env`. Note that his version is only meant for proving,
for production purposes use `Env.mkConstCached` and equality theorems to this one.
-/
def mkConst (val : Bool) (env : Env) : Entrypoint :=
  let g := env.decls.size
  let decls := env.decls.push (.const val)
  let cache := env.cache.noUpdate
  have inv := by
    intro i lhs rhs linv rinv h1 h2
    simp only [decls] at *
    simp only [Array.get_push] at h2
    split at h2
    . apply env.inv <;> assumption
    . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

end Env
