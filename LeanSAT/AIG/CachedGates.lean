import LeanSAT.AIG.Cached
import LeanSAT.AIG.CachedLemmas

namespace Env

def mkNotCached (gate : Nat) (env : Env) (hgate : gate < env.decls.size) : Entrypoint :=
  -- ¬x = true && invert x
  let constEntry := env.mkConstCached true
  have := env.mkConstCached_le_size true
  constEntry.env.mkGateCached
    constEntry.start
    gate
    false
    true
    constEntry.inv
    (by apply lt_mkConstCached_size_of_lt_env_size _ _ hgate)

def mkAndCached (lhs rhs : Nat) (env : Env) (hl : lhs < env.decls.size) (hr : rhs < env.decls.size) : Entrypoint :=
  env.mkGateCached lhs rhs false false hl hr

def mkOrCached (lhs rhs : Nat) (env : Env) (hl : lhs < env.decls.size) (hr : rhs < env.decls.size) : Entrypoint :=
  -- x or y = true && (invert (invert x && invert y))
  let auxEntry := env.mkGateCached lhs rhs true true hl hr
  let constEntry := auxEntry.env.mkConstCached true
  constEntry.env.mkGateCached
    constEntry.start
    auxEntry.start
    false
    true
    constEntry.inv
    (by apply lt_mkConstCached_size)

def mkXorCached (lhs rhs : Nat) (env : Env) (hl : lhs < env.decls.size) (hr : rhs < env.decls.size) : Entrypoint :=
  -- x xor y = (invert (invert (x && y))) && (invert ((invert x) && (invert y)))
  let aux1Entry := env.mkGateCached lhs rhs false false hl hr
  have := env.mkGateCached_le_size _ _ false false hl hr
  have h3 : lhs < aux1Entry.env.decls.size := by
    dsimp [aux1Entry] at *
    omega
  let aux2Entry := aux1Entry.env.mkGateCached
      lhs
      rhs
      true
      true
      h3
      (by apply lt_mkGateCached_size_of_lt_env_size; omega)
  aux2Entry.env.mkGateCached aux1Entry.start aux2Entry.start true true (by apply lt_mkGateCached_size) aux2Entry.inv

def mkBEqCached (lhs rhs : Nat) (env : Env) (hl : lhs < env.decls.size) (hr : rhs < env.decls.size) : Entrypoint :=
  -- a == b = (invert (a && (invert b))) && (invert ((invert a) && b))
  let aux1Entry := env.mkGateCached lhs rhs false true hl hr
  have := env.mkGateCached_le_size _ _ false true hl hr
  have h3 : lhs < aux1Entry.env.decls.size := by
    dsimp [aux1Entry] at *
    omega
  let aux2Entry :=
    aux1Entry.env.mkGateCached
      lhs
      rhs
      true
      false
      h3
      (by apply lt_mkGateCached_size_of_lt_env_size; omega)
  aux2Entry.env.mkGateCached
    aux1Entry.start
    aux2Entry.start
    true
    true
    (by apply lt_mkGateCached_size)
    aux2Entry.inv

def mkImpCached (lhs rhs : Nat) (env : Env) (hl : lhs < env.decls.size) (hr : rhs < env.decls.size) : Entrypoint :=
  -- a -> b = true && (invert (a and (invert b)))
  let auxEntry :=
    env.mkGateCached
      lhs
      rhs
      false
      true
      hl
      hr
  have := env.mkGateCached_le_size _ _ false true hl hr
  let constEntry := mkConstCached true auxEntry.env
  have := auxEntry.env.mkConstCached_le_size true
  constEntry.env.mkGateCached
    constEntry.start
    auxEntry.start
    false
    true
    constEntry.inv
    (by apply lt_mkConstCached_size)

end Env
