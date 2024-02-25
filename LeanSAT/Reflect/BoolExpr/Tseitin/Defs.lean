/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.BoolExpr.Decidable
import LeanSAT.Reflect.CNF.Relabel

namespace Gate

def toCNF (i₁ i₂ o : α) : Gate → CNF α
  | .and =>
    [[(o, false), (i₁, true)], [(o, false), (i₂, true)], [(o, true), (i₁, false), (i₂, false)]]
  | .or =>
    [[(o, true), (i₁, false)], [(o, true), (i₂, false)], [(o, false), (i₁, true), (i₂, true)]]
  | .xor =>
    [[(o, false), (i₁, true), (i₂, true)], [(o, false), (i₁, false), (i₂, false)],
      [(o, true), (i₁, false), (i₂, true)], [(o, true), (i₁, true), (i₂, false)]]
  | .beq =>
    [[(o, false), (i₁, true), (i₂, false)], [(o, false), (i₁, false), (i₂, true)],
      [(o, true), (i₁, false), (i₂, false)], [(o, true), (i₁, true), (i₂, true)]]
  | .imp =>
    [[(o, false), (i₁, false), (i₂, true)], [(o, true), (i₁, true)], [(o, true), (i₂, false)]]

end Gate

namespace CNF

def eq (x y : α) : CNF α := [[(x, true), (y, false)], [(x, false), (y, true)]]

def ne (x y : α) : CNF α := [[(x, true), (y, true)], [(x, false), (y, false)]]

end CNF

namespace BoolExpr

/-
Implementation of `BoolExpr.toCNF`.

We produce a CNF with literals labelled by `α ⊕ Nat`.
- `.inl a` represents an "input node" corresponding to a literal in the original `BoolExpr`
- `.inr j` represents a "circuit node" corresponding to
  a gate (0-ary, 1-ary, or 2-ary) in the `BoolExpr`.
-/
def toCNF' (x : BoolExpr α) : CNF (α ⊕ Nat) :=
  let (c, p) := run 0 x
  [(.inr p, true)] :: c
where
  /--
  We take as additional argument `k : Nat` which is the "next available circuit node label"
  and return an `α ⊕ Nat`, the label of the "output node".
  -/
  run (k : Nat) : BoolExpr α → CNF (α ⊕ Nat) × Nat
  | .literal a => (CNF.eq (.inl a) (.inr k), k)
  | .const b => ([[(.inr k, b)]], k)
  | .not x => match run k x with
    | (c, nx) => (CNF.ne (.inr (nx + 1)) (.inr nx) ++ c, nx + 1)
  | .gate g x y => match run k x with
    | (cx, nx) => match run (nx + 1) y with
      | (cy, ny) =>
        (g.toCNF (.inr nx) (.inr ny) (.inr (ny + 1)) ++ cx ++ cy, ny + 1)

def toCNF (x : BoolExpr Nat) : CNF Nat :=
  (toCNF' x.attach).relabel fun | .inl a => a | .inr j => x.vars + j

end BoolExpr
