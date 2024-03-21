/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Std.Data.HashMap

/-!
This module contains the basic definitions for an AIG (And-Inverter Graph) in the style of AIGNET,
as described in https://arxiv.org/pdf/1304.7861.pdf section 3. It contains an AIG definition,
a description of its semantics and basic operations to construct nodes in the AIG.
-/

open Std

theorem Array.get_push_old (as : Array α) (a : α) (h : i < as.size) : (as.push a)[i]'(by simp; omega) = as[i] := by
  simp [Array.get_push, h]

theorem Array.get_push_size (as : Array α) (a : α) : (as.push a)[as.size] = a := by
  simp [Array.get_push]

/--
A circuit node declaration. These are not recursive but instead contain indices into an `AIG`.
-/
inductive Decl (α : Type) where
  /--
  A node with a constant output value.
  -/
  | const (b : Bool)
  /--
  An input node to the circuit.
  -/
  | atom (idx : α)
  /--
  An AIG gate with configurable input nodes and polarity. `l` and `r` are the
  input node indices while `linv` and `rinv` say whether there is an inverter on
  the left or right input.
  -/
  | gate (l r : Nat) (linv rinv : Bool)
  deriving BEq, Hashable, Repr, DecidableEq

variable {α : Type} [BEq α] [Hashable α] [DecidableEq α]

/--
A `Cache` is valid with respect to a list of declarations iff:
Whenever `cache.find? decl` returns an index into `xs : Array Decl`, `xs[index] = decl`.
This predicate limits a `HashMap Decl Nat` to this behavior.
-/
inductive Cache.WF : Array (Decl α) → HashMap (Decl α) Nat → Prop where
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
def Cache (α : Type) [BEq α] [Hashable α] (decls : Array (Decl α)) :=
  { map : HashMap (Decl α) Nat // Cache.WF decls map }

/--
Create an empty `Cache`, valid with respect to any `Array Decl`.
-/
@[irreducible]
def Cache.empty (decls : Array (Decl α)) : Cache α decls := ⟨HashMap.empty, WF.empty⟩

@[inherit_doc Cache.WF.push_id, irreducible]
def Cache.noUpdate (cache : Cache α decls) : Cache α (decls.push decl) :=
  ⟨cache.val, Cache.WF.push_id cache.property⟩

@[inherit_doc Cache.WF.push_cache, irreducible]
def Cache.insert (cache : Cache α decls) (decl : Decl α) : Cache α (decls.push decl) :=
  ⟨cache.val.insert decl decls.size, Cache.WF.push_cache cache.property⟩

structure CacheHit (decls : Array (Decl α)) (decl : Decl α) where
  idx : Nat
  hbound : idx < decls.size
  hvalid : decls[idx]'hbound = decl

/--
Lookup a `decl` in a `cache`.

If this returns `some i`, `Cache.find?_poperty` can be used to demonstrate: `decls[i] = decl`.
-/
@[irreducible]
def Cache.find? (cache : Cache α decls) (decl : Decl α) : Option (CacheHit decls decl) :=
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
def IsDag (α : Type) (decls : Array (Decl α)) : Prop := ∀ i lhs rhs linv rinv (h : i < decls.size), decls[i] = .gate lhs rhs linv rinv → lhs < i ∧ rhs < i

/--
The empty array is a DAG.
-/
theorem IsDag.empty : IsDag α #[] := by
  intro i lhs rhs linv rinv h
  simp only [Array.size_toArray, List.length_nil] at h
  omega

/--
An And Inverter Graph (AIG α) together with a cache for subterm sharing.
-/
structure AIG (α : Type) [BEq α] [Hashable α] where
  /--
  The circuit itself as an `Array Decl` whose members have indices into said array.
  -/
  decls : Array (Decl α)
  /--
  The `Decl` cache, valid with respect to `decls`.
  -/
  cache : Cache α decls
  /--
  In order to be a valid AIG, `decls` must form a DAG.
  -/
  inv : IsDag α decls

namespace AIG

/--
An `AIG` with an empty AIG and cache.
-/
def empty : AIG α := { decls := #[], cache := Cache.empty #[], inv := IsDag.empty }

def mem (a : α) (aig : AIG α) : Prop := (.atom a) ∈ aig.decls

instance : Membership α (AIG α) where
  mem := mem

/--
An entrypoint into an `AIG`. This can be used to evaluate a circuit, starting at a certain node,
with `AIG.denote` or to construct bigger circuits
-/
structure Entrypoint (α : Type) [BEq α] [Hashable α] where
  /--
  The AIG that we are in.
  -/
  aig : AIG α
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
def denote (entry : Entrypoint α) (assign : α → Bool) : Bool :=
  go entry.start entry.aig.decls assign entry.inv entry.aig.inv
where
  go (x : Nat) (decls : Array (Decl α)) (assign : α → Bool) (h1 : x < decls.size) (h2 : IsDag α decls) :=
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

def unsatAt (aig : AIG α) (start : Nat) (h : start < aig.decls.size) : Prop := ∀ assign, ⟦aig, ⟨start, h⟩, assign⟧ = false
def Entrypoint.unsat (entry : Entrypoint α) : Prop := entry.aig.unsatAt entry.start entry.inv

/--
Build an AIG gate in `aig`. Note that his version is only meant for proving,
for production purposes use `AIG.mkGateCached` and equality theorems to this one.
-/
def mkGate (lhs rhs : Nat) (linv rinv : Bool) (aig : AIG α) (hl : lhs < aig.decls.size)
    (hr : rhs < aig.decls.size) : Entrypoint α :=
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
def mkAtom (n : α) (aig : AIG α) : Entrypoint α :=
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
def mkConst (val : Bool) (aig : AIG α) : Entrypoint α :=
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
