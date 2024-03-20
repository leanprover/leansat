import LeanSAT.AIG.Basic
import LeanSAT.AIG.Lemmas

namespace AIG

/--
A version of `AIG.mkGate` that uses the subterm cache in `AIG`. This version is meant for
programmming, for proving purposes use `AIG.mkGate` and equality theorems to this one.
-/
def mkGateCached (lhs rhs : Nat) (linv rinv : Bool) (aig : AIG) (hl : lhs < aig.decls.size)
    (hr : rhs < aig.decls.size) : AIG.Entrypoint :=
  let decl := .gate lhs rhs linv rinv
  match aig.cache.find? decl with
  | some hit =>
    ⟨aig, hit.idx, hit.hbound⟩
  | none =>
    let g := aig.decls.size
    let decls := aig.decls.push decl
    let cache := Cache.insert aig.cache decl
    have inv := by
      intro lhs rhs linv rinv i h1 h2
      simp only [decls] at *
      simp only [Array.get_push] at h2
      split at h2
      . apply aig.inv <;> assumption
      . injections; omega
    ⟨{ aig with decls, inv, cache }, g, by simp [g, decls]⟩

/--
A version of `AIG.mkAtom` that uses the subterm cache in `AIG`. This version is meant for
programmming, for proving purposes use `AIG.mkAtom` and equality theorems to this one.
-/
def mkAtomCached (n : Nat) (aig : AIG) : Entrypoint :=
  let decl := .atom n
  match aig.cache.find? decl with
  | some hit =>
    ⟨aig, hit.idx, hit.hbound⟩
  | none =>
    let g := aig.decls.size
    let decls := aig.decls.push decl
    let cache := aig.cache.insert decl
    have inv := by
      intro i lhs rhs linv rinv h1 h2
      simp only [decls] at *
      simp only [Array.get_push] at h2
      split at h2
      . apply aig.inv <;> assumption
      . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

/--
A version of `AIG.mkConst` that uses the subterm cache in `AIG`. This version is meant for
programmming, for proving purposes use `AIG.mkGate` and equality theorems to this one.
-/
def mkConstCached (val : Bool) (aig : AIG) : Entrypoint :=
  let decl := .const val
  match aig.cache.find? decl with
  | some hit =>
    ⟨aig, hit.idx, hit.hbound⟩
  | none =>
    let g := aig.decls.size
    let decls := aig.decls.push decl
    let cache := aig.cache.insert decl
    have inv := by
      intro i lhs rhs linv rinv h1 h2
      simp only [decls] at *
      simp only [Array.get_push] at h2
      split at h2
      . apply aig.inv <;> assumption
      . contradiction
  ⟨{ decls, inv, cache }, g, by simp [g, decls]⟩

end AIG
