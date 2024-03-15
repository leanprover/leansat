import LeanSAT.AIG.Basic
import LeanSAT.Reflect.CNF.Basic
import LeanSAT.Reflect.CNF.Relabel

namespace Env

def toCNF (entry : Entrypoint) : CNF Nat :=
  let cnf := go entry.env 0 ⟨entry.start, entry.inv⟩ (by omega) []
  cnf.relabel fun | .inl var => var.val | .inr var => entry.env.decls.size + var
where
  go (env : Env) (idx : Nat) (upper : Fin env.decls.size) (h : idx ≤ upper)
      (curr : CNF ((Fin env.decls.size) ⊕ Nat)) : CNF ((Fin env.decls.size) ⊕ Nat) :=
    let decl := env.decls[idx]'sorry
    let declCnf : CNF ((Fin env.decls.size) ⊕ Nat) :=
      match decl with
      | .const b => sorry
      | .atom a => sorry
      | .gate lhs rhs linv rinv => sorry
    let newCnf := curr ++ declCnf
    if h2:idx = upper then
       newCnf
    else
       go env (idx + 1) upper (by omega) newCnf
  termination_by upper.val - idx

end Env
