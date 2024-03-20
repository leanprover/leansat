import Std.Data.HashMap
open Std

theorem Array.get_push_old (as : Array α) (a : α) (h : i < as.size) : (as.push a)[i]'(by simp; omega) = as[i] := by
  simp [Array.get_push, h]

theorem Array.get_push_size (as : Array α) (a : α) : (as.push a)[as.size] = a := by
  simp [Array.get_push]

/--
A circuit node declaration. These are not recursive but instead contain indices into an `AIG`.
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
  deriving BEq, Hashable, Repr, DecidableEq

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
@[irreducible]
def Cache.empty (decls : Array Decl) : Cache decl := ⟨HashMap.empty, WF.empty⟩

@[inherit_doc Cache.WF.push_id, irreducible]
def Cache.noUpdate (cache : Cache decls) : Cache (decls.push decl) :=
  ⟨cache.val, Cache.WF.push_id cache.property⟩

@[inherit_doc Cache.WF.push_cache, irreducible]
def Cache.insert (cache : Cache decls) (decl : Decl) : Cache (decls.push decl) :=
  ⟨cache.val.insert decl decls.size, Cache.WF.push_cache cache.property⟩

structure CacheHit (decls : Array Decl) (decl : Decl) where
  idx : Nat
  hbound : idx < decls.size
  hvalid : decls[idx]'hbound = decl

/--
Lookup a `decl` in a `cache`.

If this returns `some i`, `Cache.find?_poperty` can be used to demonstrate: `decls[i] = decl`.
-/
@[irreducible]
def Cache.find? (cache : Cache decls) (decl : Decl) : Option (CacheHit decls decl) :=
  match cache.val.find? decl with
  | some hit =>
    /-
    TODO: There are two ways around these checks:
    1. If we are desperate for performance we can axiomatize `Cache.find?_bounds` and
       `Cache.find?_property`. These theorems are valid even without these checks
    2. Once we have a proper `HashMap` theory we can use `Cache.WF` to show that the theorems hold
       without checks.

    Note that both of these checks are only O(1) so this constitutes at most a constant overhead.
    -/
    if h1:hit < decls.size then
      if h2:decls[hit]'h1 = decl then
        some ⟨hit, h1, h2⟩
      else
        none
    else
      none
  | none => none

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
structure AIG where
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

namespace AIG

/--
An `AIG` with an empty AIG and cache.
-/
def empty : AIG := { decls := #[], cache := Cache.empty #[], inv := IsDag.empty }

/--
An entrypoint into an `AIG`. This can be used to evaluate a circuit, starting at a certain node,
with `AIG.denote` or to construct bigger circuits
-/
structure Entrypoint where
  /--
  The AIG that we are in.
  -/
  aig : AIG
  /--
  The AIG node at which to begin evaluation.
  -/
  start : Nat
  /--
  The AIG node must be within bounds.
  -/
  inv : start < aig.decls.size

/--
Evaluate an `AIG.Entrypoint` using some assignment for atoms.
-/
def denote (entry : Entrypoint) (assign : Nat → Bool) : Bool :=
  go entry.start entry.aig.decls assign entry.inv entry.aig.inv
where
  go (x : Nat) (decls : Array Decl) (assign : Nat → Bool) (h1 : x < decls.size) (h2 : IsDag decls) :=
    match h3 : decls[x] with
    | .const b => b
    | .atom v => assign v
    | .gate lhs rhs linv rinv =>
      have := h2 x _ _ _ _ h1 h3
      let lval := go lhs decls assign (by omega) h2
      let rval := go rhs decls assign (by omega) h2
      xor lval linv && xor rval rinv

scoped syntax "⟦" term ", " term "⟧" : term
scoped syntax "⟦" term ", " "⟨" term ", " term "⟩" ", " term "⟧" : term

macro_rules
| `(⟦$entry, $assign⟧) => `(denote $entry $assign)
| `(⟦$aig, ⟨$start, $hbound⟩, $assign⟧) => `(denote (Entrypoint.mk $aig $start $hbound) $assign)

@[app_unexpander AIG.denote]
def unexpandDenote : Lean.PrettyPrinter.Unexpander
  | `($(_) {aig := $aig, start := $start, inv := $hbound} $assign) => `(⟦$aig, ⟨$start, $hbound⟩, $assign⟧)
  | `($(_) $entry $assign) => `(⟦$entry, $assign⟧)
  | _ => throw ()

def unsatAt (aig : AIG) (start : Nat) (h : start < aig.decls.size) : Prop := ∀ assign, ⟦aig, ⟨start, h⟩, assign⟧ = false
def Entrypoint.unsat (entry : Entrypoint) : Prop := entry.aig.unsatAt entry.start entry.inv

/--
Build an AIG gate in `aig`. Note that his version is only meant for proving,
for production purposes use `AIG.mkGateCached` and equality theorems to this one.
-/
def mkGate (lhs rhs : Nat) (linv rinv : Bool) (aig : AIG) (hl : lhs < aig.decls.size)
    (hr : rhs < aig.decls.size) : Entrypoint :=
  let g := aig.decls.size
  let decls := aig.decls.push (.gate lhs rhs linv rinv)
  let cache := aig.cache.noUpdate
  have inv := by
    intro i lhs rhs linv rinv h1 h2
    simp only [decls, Array.get_push] at h2
    split at h2
    . apply aig.inv <;> assumption
    . injections; omega
  ⟨{ aig with decls, inv, cache }, g, by simp [g, decls]⟩

/--
Add a new input node to the AIG in `aig`. Note that his version is only meant for proving,
for production purposes use `AIG.mkAtomCached` and equality theorems to this one.
-/
def mkAtom (n : Nat) (aig : AIG) : Entrypoint :=
  let g := aig.decls.size
  let decls := aig.decls.push (.atom n)
  let cache := aig.cache.noUpdate
  have inv := by
    intro i lhs rhs linv rinv h1 h2
    simp only [decls] at *
    simp only [Array.get_push] at h2
    split at h2
    . apply aig.inv <;> assumption
    . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

/--
Build an constant node in `aig`. Note that his version is only meant for proving,
for production purposes use `AIG.mkConstCached` and equality theorems to this one.
-/
def mkConst (val : Bool) (aig : AIG) : Entrypoint :=
  let g := aig.decls.size
  let decls := aig.decls.push (.const val)
  let cache := aig.cache.noUpdate
  have inv := by
    intro i lhs rhs linv rinv h1 h2
    simp only [decls] at *
    simp only [Array.get_push] at h2
    split at h2
    . apply aig.inv <;> assumption
    . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

end AIG
