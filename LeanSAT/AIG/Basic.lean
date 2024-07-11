/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Std.Data.HashMap
import Std.Data.HashSet

/-!
This module contains the basic definitions for an AIG (And-Inverter Graph) in the style of AIGNET,
as described in https://arxiv.org/pdf/1304.7861.pdf section 3. It contains an AIG definition,
a description of its semantics and basic operations to construct nodes in the AIG.
-/

open Std

theorem Array.lt_of_get {x : α} (as : Array α) {idx : Nat} {hidx : idx < as.size} (_h : as[idx]'hidx = x) : idx < as.size := by
  exact hidx

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
  deriving Hashable, Repr, DecidableEq, Inhabited

variable {α : Type} [Hashable α] [DecidableEq α]

/--
A `Cache` is valid with respect to a list of declarations iff:
Whenever `cache.find? decl` returns an index into `xs : Array Decl`, `xs[index] = decl`.
This predicate limits a `HashMap Decl Nat` to this behavior.
-/
inductive Cache.WF : Array (Decl α) → HashMap (Decl α) Nat → Prop where
  /--
  An empty `Cache` is valid for any `Array Decl` as it never has a hit.
  -/
  | empty : Cache.WF decls {}
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
def Cache (α : Type) [DecidableEq α] [Hashable α] (decls : Array (Decl α)) :=
  { map : HashMap (Decl α) Nat // Cache.WF decls map }

/--
Create an empty `Cache`, valid with respect to any `Array Decl`.
-/
@[irreducible]
def Cache.empty (decls : Array (Decl α)) : Cache α decls := ⟨{}, WF.empty⟩

@[inherit_doc Cache.WF.push_id, irreducible]
def Cache.noUpdate (cache : Cache α decls) : Cache α (decls.push decl) :=
  ⟨cache.val, Cache.WF.push_id cache.property⟩

/-
We require the `decls` as an explicit attribute because we use `decls.size` so accidentally mutating
`decls` before calling `Cache.insert` will destroy `decl` linearity.
-/
@[inherit_doc Cache.WF.push_cache, irreducible]
def Cache.insert (decls : Array (Decl α)) (cache : Cache α decls) (decl : Decl α)
    : Cache α (decls.push decl) :=
  ⟨cache.val.insert decl decls.size, Cache.WF.push_cache cache.property⟩

structure CacheHit (decls : Array (Decl α)) (decl : Decl α) where
  idx : Nat
  hbound : idx < decls.size
  hvalid : decls[idx]'hbound = decl

/--
All indices, found in a `Cache` that is valid with respect to some `decls`, are within bounds of `decls`.
-/
theorem Cache.get?_bounds {decls : Array (Decl α)} {idx : Nat} (c : Cache α decls) (decl : Decl α)
    (hfound : c.val[decl]? = some idx) : idx < decls.size := by
  rcases c with ⟨cache, hcache⟩
  induction hcache with
  | empty => simp at hfound
  | push_id wf ih =>
    specialize ih hfound
    simp
    omega
  | push_cache wf ih =>
    rename_i decl'
    simp only [HashMap.getElem?_insert] at hfound
    match heq:decl == decl' with
    | true =>
      simp only [heq, cond_true, Option.some.injEq] at hfound
      simp
      omega
    | false =>
      simp only [heq, cond_false] at hfound
      specialize ih hfound
      simp
      omega

/--
If `Cache.find? decl` returns `some i` then `decls[i] = decl` holds.
-/
theorem Cache.get?_property {decls : Array (Decl α)} {idx : Nat} (c : Cache α decls) (decl : Decl α)
    (hfound : c.val[decl]? = some idx) : decls[idx]'(Cache.get?_bounds c decl hfound) = decl := by
  rcases c with ⟨cache, hcache⟩
  induction hcache generalizing decl with
  | empty => simp at hfound
  | push_id wf ih =>
    rw [Array.get_push]
    split
    . apply ih
      simp [hfound]
    . next hbounds =>
      exfalso
      apply hbounds
      specialize ih _ hfound
      apply Array.lt_of_get
      assumption
  | push_cache wf ih =>
    rename_i decl'
    rw [Array.get_push]
    split
    . simp only [HashMap.getElem?_insert] at hfound
      match heq:decl == decl' with
      | true =>
        simp [heq] at hfound
        omega
      | false =>
        simp [heq] at hfound
        apply ih
        assumption
    . next hbounds =>
      simp only [HashMap.getElem?_insert] at hfound
      match heq:decl == decl' with
      | true =>
        apply Eq.symm
        simpa using heq
      | false =>
        exfalso
        apply hbounds
        simp [heq] at hfound
        specialize ih _ hfound
        apply Array.lt_of_get
        assumption

/--
Lookup a `Decl` in a `Cache`.
-/
opaque Cache.get? (cache : Cache α decls) (decl : Decl α) : Option (CacheHit decls decl) :=
  /-
  This function is marked as `opaque` to make sure it never, ever gets unfolded anywhere.
  Unfolding it will often always cause `HashMap.find?` to be symbolically evaluated by reducing
  it either in `whnf` or in the kernel. This causes *huge* performance issues in practice.
  The function can still be fully verified as all the proofs we need are in `CacheHit`.
  -/
  match hfound:cache.val[decl]? with
  | some hit =>
    some ⟨hit, Cache.get?_bounds _ _ hfound, Cache.get?_property _ _ hfound⟩
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
structure AIG (α : Type) [DecidableEq α] [Hashable α] where
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
A reference to a node within an AIG.
-/
structure Ref (aig : AIG α) where
  gate : Nat
  hgate : gate < aig.decls.size

@[inline]
def Ref.cast {aig1 aig2 : AIG α} (ref : Ref aig1)
    (h : aig1.decls.size ≤ aig2.decls.size) : Ref aig2 :=
  { ref with hgate := by have := ref.hgate; omega }

structure BinaryInput (aig : AIG α) where
  lhs : Ref aig
  rhs : Ref aig

@[inline]
def BinaryInput.cast {aig1 aig2 : AIG α} (input : BinaryInput aig1)
    (h : aig1.decls.size ≤ aig2.decls.size) : BinaryInput aig2 :=
  { input with lhs := input.lhs.cast h, rhs := input.rhs.cast h }

structure TernaryInput (aig : AIG α) where
  discr : Ref aig
  lhs : Ref aig
  rhs : Ref aig

@[inline]
def TernaryInput.cast {aig1 aig2 : AIG α} (input : TernaryInput aig1)
    (h : aig1.decls.size ≤ aig2.decls.size) : TernaryInput aig2 :=
  { input with discr := input.discr.cast h, lhs := input.lhs.cast h, rhs := input.rhs.cast h }

/--
An entrypoint into an `AIG`. This can be used to evaluate a circuit, starting at a certain node,
with `AIG.denote` or to construct bigger circuits
-/
structure Entrypoint (α : Type) [DecidableEq α] [Hashable α] where
  /--
  The AIG that we are in.
  -/
  aig : AIG α
  /--
  The reference to the node in `aig` that this `Entrypoint` targets.
  -/
  ref : Ref aig

/--
Transform an entrypoint into a graphviz compatible format.
StateM collects the array indices for all occuring nodes and computes the edges on the way.
Afterwards generate the node declarations once.
-/
def toGraphviz {α : Type} [DecidableEq α] [ToString α] [Hashable α] (entry : Entrypoint α) : String :=
  let ⟨⟨decls, _, hinv⟩, ⟨idx, h⟩⟩ := entry
  let (dag, s) := go "" decls hinv idx h |>.run .empty
  let nodes := s.fold (fun x y ↦ x ++ toGraphvizString decls y) ""
  "Digraph AIG {" ++ nodes ++ dag ++ "}"
where
  go {α : Type} [DecidableEq α] [ToString α] [Hashable α] (acc : String) (decls : Array (Decl α)) (hinv : IsDag α decls)
      (idx : Nat) (hidx : idx < decls.size) : StateM (HashSet (Fin decls.size)) String := do
    let fidx : Fin decls.size := Fin.mk idx hidx
    if (← get).contains fidx then
      return acc
    modify (fun s ↦ s.insert fidx)
    match elem : decls[idx] with
    | Decl.const _ => return acc
    | Decl.atom _ => return acc
    | Decl.gate lidx ridx linv rinv =>
      let curr := s!"{idx} -> {lidx}{invEdgeStyle linv}; {idx} -> {ridx}{invEdgeStyle rinv};"
      let hlr := hinv idx lidx ridx linv rinv hidx elem
      let laig ← go (acc ++ curr) decls hinv lidx (by omega)
      go laig decls hinv ridx (by omega)
  invEdgeStyle (isInv : Bool) : String :=
    if isInv then " [color=red]" else " [color=blue]"
  toGraphvizString {α : Type} [DecidableEq α] [ToString α] [Hashable α] (decls : Array (Decl α))
      (idx : Fin decls.size) : String :=
    match decls[idx] with
    | Decl.const b => s!"{idx} [label=\"{b}\", shape=box];"
    | Decl.atom i => s!"{idx} [label=\"{i}\", shape=doublecircle];"
    | Decl.gate _ _ _ _ => s!"{idx} [label=\"{idx} ∧\",shape=trapezium];"

structure RefStream (aig : AIG α) (length : Nat) where
  refs : Array Nat
  hlen : refs.size = length
  hrefs : ∀ (h : i < length), refs[i] < aig.decls.size

structure RefStreamEntry (α : Type) [DecidableEq α] [Hashable α] [DecidableEq α] (length : Nat) where
  aig : AIG α
  stream : RefStream aig length

structure ShiftTarget (aig : AIG α) (w : Nat) where
  stream : AIG.RefStream aig w
  distance : Nat

structure ExtendTarget (aig : AIG α) (newWidth : Nat) where
  w : Nat
  stream : AIG.RefStream aig w

/--
Evaluate an `AIG.Entrypoint` using some assignment for atoms.
-/
def denote (entry : Entrypoint α) (assign : α → Bool) : Bool :=
  go entry.ref.gate entry.aig.decls assign entry.ref.hgate entry.aig.inv
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
scoped syntax "⟦" term ", " term ", " term "⟧" : term

macro_rules
| `(⟦$entry, $assign⟧) => `(denote $entry $assign)
| `(⟦$aig, $ref, $assign⟧) => `(denote (Entrypoint.mk $aig $ref) $assign)

@[app_unexpander AIG.denote]
def unexpandDenote : Lean.PrettyPrinter.Unexpander
  | `($(_) {aig := $aig, start := $start, inv := $hbound} $assign) => `(⟦$aig, ⟨$start, $hbound⟩, $assign⟧)
  | `($(_) $entry $assign) => `(⟦$entry, $assign⟧)
  | _ => throw ()

def unsatAt (aig : AIG α) (start : Nat) (h : start < aig.decls.size) : Prop := ∀ assign, ⟦aig, ⟨start, h⟩, assign⟧ = false
def Entrypoint.unsat (entry : Entrypoint α) : Prop := entry.aig.unsatAt entry.ref.gate entry.ref.hgate

/--
An input to an AIG gate.
-/
structure Fanin (aig : AIG α) where
  /--
  The node we are referring to.
  -/
  ref : Ref aig
  /--
  Whether the node is inverted
  -/
  inv : Bool

@[inline]
def Fanin.cast {aig1 aig2 : AIG α} (fanin : Fanin aig1)
    (h : aig1.decls.size ≤ aig2.decls.size)
    : Fanin aig2 :=
  { fanin with ref := fanin.ref.cast h }

/--
The input type for creating AIG and gates from scratch.
-/
structure GateInput (aig : AIG α) where
  lhs : Fanin aig
  rhs : Fanin aig

@[inline]
def GateInput.cast {aig1 aig2 : AIG α} (input : GateInput aig1)
    (h : aig1.decls.size ≤ aig2.decls.size)
    : GateInput aig2 :=
  { input with lhs := input.lhs.cast h, rhs := input.rhs.cast h }

/--
Build an AIG gate in `aig`. Note that his version is only meant for proving,
for production purposes use `AIG.mkGateCached` and equality theorems to this one.
-/
def mkGate (aig : AIG α) (input : GateInput aig) : Entrypoint α :=
  let lhs := input.lhs
  let rhs := input.rhs
  let g := aig.decls.size
  let decls := aig.decls.push (.gate lhs.ref.gate rhs.ref.gate lhs.inv rhs.inv)
  let cache := aig.cache.noUpdate
  have inv := by
    intro i lhs' rhs' linv' rinv' h1 h2
    simp only [decls, Array.get_push] at h2
    split at h2
    . apply aig.inv <;> assumption
    . injections
      have := lhs.ref.hgate
      have := rhs.ref.hgate
      omega
  ⟨{ aig with decls, inv, cache }, ⟨g, by simp [g, decls]⟩⟩

/--
Add a new input node to the AIG in `aig`. Note that his version is only meant for proving,
for production purposes use `AIG.mkAtomCached` and equality theorems to this one.
-/
def mkAtom (aig : AIG α) (n : α) : Entrypoint α :=
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
  ⟨{ decls, inv, cache }, ⟨g, by simp [g, decls]⟩⟩

/--
Build an constant node in `aig`. Note that his version is only meant for proving,
for production purposes use `AIG.mkConstCached` and equality theorems to this one.
-/
def mkConst (aig : AIG α) (val : Bool) : Entrypoint α :=
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
  ⟨{ decls, inv, cache }, ⟨g, by simp [g, decls]⟩⟩

end AIG
