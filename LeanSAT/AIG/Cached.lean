import LeanSAT.AIG.Basic
import LeanSAT.AIG.Lemmas

namespace Env

/--
A version of `Env.mkGate` that uses the subterm cache in `Env`. This version is meant for
programmming, for proving purposes use `Env.mkGate` and equality theorems to this one.
-/
def mkGateCached (lhs rhs : Nat) (linv rinv : Bool) (env : Env) (hl : lhs < env.decls.size)
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
A version of `Env.mkAtom` that uses the subterm cache in `Env`. This version is meant for
programmming, for proving purposes use `Env.mkAtom` and equality theorems to this one.
-/
def mkAtomCached (n : Nat) (env : Env) : Entrypoint :=
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
A version of `Env.mkConst` that uses the subterm cache in `Env`. This version is meant for
programmming, for proving purposes use `Env.mkGate` and equality theorems to this one.
-/
def mkConstCached (val : Bool) (env : Env) : Entrypoint :=
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

end Env
