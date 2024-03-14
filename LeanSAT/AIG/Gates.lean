import LeanSAT.AIG.Basic
import LeanSAT.AIG.Lemmas

namespace Env

def mkNot (gate : Nat) (env : Env) (hgate : gate < env.decls.size) : Entrypoint :=
  -- ¬x = true && invert x
  let constEntry := env.mkConst true
  have := env.mkConst_le_size true
  constEntry.env.mkGate
    constEntry.start
    gate
    false
    true
    constEntry.inv
    (by apply lt_mkConst_size_of_lt_env_size _ _ hgate)

def mkAnd (lhs rhs : Nat) (env : Env) (hl : lhs < env.decls.size) (hr : rhs < env.decls.size) : Entrypoint :=
  env.mkGate lhs rhs false false hl hr

def mkOr (lhs rhs : Nat) (env : Env) (hl : lhs < env.decls.size) (hr : rhs < env.decls.size) : Entrypoint :=
  -- x or y = true && (invert (invert x && invert y))
  let auxEntry := env.mkGate lhs rhs true true hl hr
  let constEntry := auxEntry.env.mkConst true
  constEntry.env.mkGate
    constEntry.start
    auxEntry.start
    false
    true
    constEntry.inv
    (by apply lt_mkConst_size)

def mkXor (lhs rhs : Nat) (env : Env) (hl : lhs < env.decls.size) (hr : rhs < env.decls.size) : Entrypoint :=
  -- x xor y = (invert (invert (x && y))) && (invert ((invert x) && (invert y)))
  let aux1Entry := env.mkGate lhs rhs false false hl hr
  have := env.mkGate_le_size _ _ false false hl hr
  have h3 : lhs < aux1Entry.env.decls.size := by
    dsimp [aux1Entry] at *
    omega
  let aux2Entry := aux1Entry.env.mkGate
      lhs
      rhs
      true
      true
      h3
      (by apply lt_mkGate_size_of_lt_env_size; omega)
  aux2Entry.env.mkGate aux1Entry.start aux2Entry.start true true (by apply lt_mkGate_size) aux2Entry.inv

def mkBEq (lhs rhs : Nat) (env : Env) (hl : lhs < env.decls.size) (hr : rhs < env.decls.size) : Entrypoint :=
  -- a == b = (invert (a && (invert b))) && (invert ((invert a) && b))
  let aux1Entry := env.mkGate lhs rhs false true hl hr
  have := env.mkGate_le_size _ _ false true hl hr
  have h3 : lhs < aux1Entry.env.decls.size := by
    dsimp [aux1Entry] at *
    omega
  let aux2Entry :=
    aux1Entry.env.mkGate
      lhs
      rhs
      true
      false
      h3
      (by apply lt_mkGate_size_of_lt_env_size; omega)
  aux2Entry.env.mkGate
    aux1Entry.start
    aux2Entry.start
    true
    true
    (by apply lt_mkGate_size)
    aux2Entry.inv

def mkImp (lhs rhs : Nat) (env : Env) (hl : lhs < env.decls.size) (hr : rhs < env.decls.size) : Entrypoint :=
  -- a -> b = true && (invert (a and (invert b)))
  let auxEntry :=
    env.mkGate
      lhs
      rhs
      false
      true
      hl
      hr
  have := env.mkGate_le_size _ _ false true hl hr
  let constEntry := mkConst true auxEntry.env
  have := auxEntry.env.mkConst_le_size true
  constEntry.env.mkGate
    constEntry.start
    auxEntry.start
    false
    true
    constEntry.inv
    (by apply lt_mkConst_size)

end Env
