/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
import LeanSAT.Sat.Basic
import LeanSAT.LRAT.Clause

namespace LRAT

open Sat

/-- Typeclass for formulas. An instance [Formula α β σ] indicates that σ is
    the type of a formula with variables of type α, clauses of type β, and clause ids of type Nat -/
class Formula (α : outParam (Type u)) (β : outParam (Type v)) [Clause α β] (σ : Type w) [HSat α σ] where
  toList : σ → List β -- A function used exclusively for defining Formula's satisfiability semantics
  readyForRupAdd : σ → Prop -- A predicate that indicates whether a formula can soundly be passed into performRupAdd
  readyForRatAdd : σ → Prop -- A predicate that indicates whether a formula can soundly be passed into performRatAdd
  ofArray : Array (Option β) → σ
  ofArray_readyForRupAdd : ∀ arr : Array (Option β), readyForRupAdd (ofArray arr)
  ofArray_readyForRatAdd : ∀ arr : Array (Option β), readyForRatAdd (ofArray arr)
  insert : σ → β → σ
  insert_iff : ∀ f : σ, ∀ c1 : β, ∀ c2 : β,
    c2 ∈ toList (insert f c1) ↔ c2 = c1 ∨ c2 ∈ toList f
  insert_readyForRupAdd : ∀ f : σ, ∀ c : β, readyForRupAdd f → readyForRupAdd (insert f c)
  insert_readyForRatAdd : ∀ f : σ, ∀ c : β, readyForRatAdd f → readyForRatAdd (insert f c)
  delete : σ → Array Nat → σ
  delete_subset : ∀ f : σ, ∀ arr : Array Nat, ∀ c : β,
    c ∈ toList (delete f arr) → c ∈ toList f
  delete_readyForRupAdd : ∀ f : σ, ∀ arr : Array Nat, readyForRupAdd f → readyForRupAdd (delete f arr)
  delete_readyForRatAdd : ∀ f : σ, ∀ arr : Array Nat, readyForRatAdd f → readyForRatAdd (delete f arr)
  formulaHSat_def : ∀ p : α → Bool, ∀ f : σ, HSat.eval p f = (toList f).all (fun c => p ⊨ c)
  performRupAdd : σ → β → Array Nat → σ × Bool
  rupAdd_result : ∀ f : σ, ∀ c : β, ∀ rupHints : Array Nat, ∀ f' : σ,
    readyForRupAdd f → performRupAdd f c rupHints = (f', true) → f' = insert f c
  rupAdd_sound : ∀ f : σ, ∀ c : β, ∀ rupHints : Array Nat, ∀ f' : σ,
    readyForRupAdd f → performRupAdd f c rupHints = (f', true) → Sat.liff α f f'
  performRatAdd : σ → β → Literal α → Array Nat → Array (Nat × Array Nat) → σ × Bool
  ratAdd_result :
    ∀ f : σ, ∀ c : β, ∀ p : Literal α, ∀ rupHints : Array Nat, ∀ ratHints : Array (Nat × Array Nat), ∀ f' : σ,
    readyForRatAdd f → p ∈ Clause.toList c → performRatAdd f c p rupHints ratHints = (f', true) → f' = insert f c
  ratAdd_sound :
    ∀ f : σ, ∀ c : β, ∀ p : Literal α, ∀ rupHints : Array Nat, ∀ ratHints : Array (Nat × Array Nat), ∀ f' : σ,
    readyForRatAdd f → p ∈ Clause.toList c → performRatAdd f c p rupHints ratHints = (f', true) → Sat.equisat α f f'
  dimacs : σ → String
  dbg_info : σ → String
