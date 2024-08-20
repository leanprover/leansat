/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Std.Data.HashMap
import Lean.Meta.AppBuilder
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Basic

namespace LeanSAT
namespace BVDecide

open Lean
open Lean.Meta
open Lean.Elab.Tactic.BVDecide

/--
The state of the reflection monad
-/
structure State where
  /--
  The atoms encountered so far. Saved as a map from `BitVec` expressions to a width × atomNumber
  pair.
  -/
  atoms : Std.HashMap Expr (Nat × Nat) := {}

/--
The reflection monad, used to track `BitVec` variables that we see as we traverse the context.
-/
abbrev M := StateRefT State MetaM

namespace M

/--
Run a reflection computation as a `MetaM` one.
-/
def run (m : M α) : MetaM α :=
  m.run' { } { }

/--
Retrieve the atoms as pairs of their width and expression.
-/
def atoms : M (List (Nat × Expr)) := do
  let sortedAtoms := (← getThe State).atoms.toArray.qsort (·.2.2 < ·.2.2)
  return sortedAtoms.map (fun (expr, width, _) => (width, expr)) |>.toList

/--
Retrieve a `BitVec.Assignment` representing the atoms we found so far.
-/
def atomsAssignment : M Expr := do
  let as ← atoms
  let packed :=
    as.map (fun (width, expr) => mkApp2 (mkConst ``BVExpr.PackedBitVec.mk) (toExpr width) expr)
  let packedType := mkConst ``BVExpr.PackedBitVec
  mkListLit packedType packed

/--
Look up an expression in the atoms, recording it if it has not previously appeared.
-/
def lookup (e : Expr) (width : Nat) : M Nat := do
  match (← getThe State).atoms[e]? with
  | some (width', ident) =>
    if width != width' then
      panic! "The same atom occurs with different widths, this is a bug"
    return ident
  | none =>
  trace[bv] "New atom of width {width}: {e}"
  let ident ← modifyGetThe State fun s =>
    (s.atoms.size, { s with atoms := s.atoms.insert e (width, s.atoms.size) })
  return ident

end M

end BVDecide
end LeanSAT
