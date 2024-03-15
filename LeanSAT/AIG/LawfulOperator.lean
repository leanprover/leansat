import LeanSAT.AIG.Basic
import LeanSAT.AIG.Lemmas

namespace Env

abbrev UnaryOperator := (gate : Nat) → (env : Env) → (gate < env.decls.size) → Entrypoint

class LawfulUnaryOperator (f : UnaryOperator) where
  le_size : ∀ (env : Env) (gate : Nat) (hgate), env.decls.size ≤ (f gate env hgate).env.decls.size
  decl_eq : ∀ (env : Env) (gate : Nat) (idx : Nat) (h1 : idx < env.decls.size) (hgate) (h2),
    (f gate env hgate).env.decls[idx]'h2 = env.decls[idx]'h1

namespace LawfulUnaryOperator

variable {f : UnaryOperator} [LawfulUnaryOperator f]

theorem IsPrefix_env (env : Env) (gate : Nat) {hgate} :
    IsPrefix env.decls (f gate env hgate).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply decl_eq
  . apply le_size

theorem lt_mkNotCached_size (entry : Entrypoint) (gate : Nat) (hgate) :
    entry.start < (f gate entry.env hgate).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (f gate entry.env hgate).env.decls.size := by
    apply le_size
  omega

theorem lt_size_of_lt_env_size (env : Env) (gate : Nat) (hgate) (h : x < env.decls.size)
    : x < (f gate env hgate).env.decls.size := by
  have := le_size (f := f) env gate hgate
  omega

theorem le_size_of_le_env_size (env : Env) (gate : Nat) (hgate) (h : x ≤ env.decls.size)
    : x ≤ (f gate env hgate).env.decls.size := by
  have := le_size (f := f) env gate hgate
  omega

@[simp]
theorem denote_entry (entry : Entrypoint) {hgate} {h} :
    ⟦(f gate entry.env hgate).env, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_env_eq
  apply IsPrefix_env

theorem denote_mem_prefix {env : Env} {hgate} (h) :
    ⟦(f gate env hgate).env, ⟨start, by apply lt_size_of_lt_env_size; omega⟩, assign⟧
      =
    ⟦env, ⟨start, h⟩, assign⟧ :=  by
  rw [denote_entry ⟨env, start, h⟩]

end LawfulUnaryOperator

abbrev BinaryOperator := (lhs rhs : Nat) → (env : Env) → (lhs < env.decls.size) → (rhs < env.decls.size) → Entrypoint

class LawfulBinaryOperator (f : BinaryOperator) where
  le_size : ∀ (env : Env) (lhs rhs : Nat) (hl) (hr), env.decls.size ≤ (f lhs rhs env hl hr).env.decls.size
  decl_eq : ∀ (env : Env) (lhs rhs : Nat) (idx : Nat) (h1 : idx < env.decls.size) (hl) (hr) (h2),
    (f lhs rhs env hl hr).env.decls[idx]'h2 = env.decls[idx]'h1

namespace LawfulBinaryOperator

variable {f : BinaryOperator} [LawfulBinaryOperator f]

theorem IsPrefix_env (env : Env) (lhs rhs : Nat) {hl} {hr} :
    IsPrefix env.decls (f lhs rhs env hl hr).env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply decl_eq
  . apply le_size

theorem lt_size (entry : Entrypoint) (lhs hrs : Nat) (hl) (hr)
    : entry.start < (f lhs rhs entry.env hl hr).env.decls.size := by
  have h1 := entry.inv
  have h2 : entry.env.decls.size ≤ (f lhs rhs entry.env hl hr).env.decls.size := by
    apply le_size
  omega

theorem lt_size_of_lt_env_size (env : Env) (lhs rhs : Nat) (hl hr)
    (h : x < env.decls.size)
    : x < (f lhs rhs env hl hr).env.decls.size := by
  have := le_size (f := f) env lhs rhs hl hr
  omega

@[simp]
theorem denote_entry (entry : Entrypoint) {hl} {hr} {h} :
    ⟦(f lhs rhs entry.env hl hr).env, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ :=  by
  apply denote.eq_of_env_eq
  apply IsPrefix_env

theorem denote_mem_prefix {env : Env} {hl} {hr} (h) :
    ⟦(f lhs rhs env hl hr).env, ⟨start, (by apply lt_size_of_lt_env_size; omega)⟩, assign⟧
      =
    ⟦env, ⟨start, h⟩, assign⟧ :=  by
  rw [denote_entry ⟨env, start, h⟩]

end LawfulBinaryOperator

end Env
