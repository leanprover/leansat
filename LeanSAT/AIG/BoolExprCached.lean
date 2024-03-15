import LeanSAT.AIG.CachedGates
import LeanSAT.AIG.CachedGatesLemmas
import LeanSAT.AIG.BoolExpr

namespace Env

-- lines such as: ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩
-- are slow in Meta.check
-- TODO: minimize
/--
Turn a `BoolExprNat` into an AIG + entrypoint. Note that this version is meant for programming
purposes. For proving use `Env.ofBoolExprNat` and equality theorems.
-/
def ofBoolExprNatCached (expr : BoolExprNat) : Entrypoint :=
  go expr Env.empty |>.val
where
  go (expr : BoolExprNat) (env : Env) : { entry : Entrypoint // env.decls.size ≤ entry.env.decls.size } :=
    match expr with
    | .literal var => ⟨env.mkAtomCached var, (by apply Env.mkAtomCached_le_size)⟩
    | .const val => ⟨env.mkConstCached val, (by apply Env.mkConstCached_le_size)⟩
    | .not expr =>
      let ⟨exprEntry, _⟩ := go expr env
      let ret := exprEntry.env.mkNotCached exprEntry.start exprEntry.inv
      have := mkNotCached_le_size exprEntry.env exprEntry.start exprEntry.inv
      ⟨ret, by dsimp [ret] at *; omega⟩
    | .gate g lhs rhs =>
      let ⟨lhsEntry, _⟩ := go lhs env
      let ⟨rhsEntry, _⟩ := go rhs lhsEntry.env
      have h1 : lhsEntry.start < Array.size rhsEntry.env.decls := by
        have := lhsEntry.inv
        omega
      match g with
      | .and =>
        let ret := rhsEntry.env.mkAndCached lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkAndCached_le_size rhsEntry.env lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .or =>
        let ret := rhsEntry.env.mkOrCached lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkOrCached_le_size rhsEntry.env lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .xor =>
        let ret := rhsEntry.env.mkXorCached lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkXorCached_le_size rhsEntry.env lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .beq =>
        let ret := rhsEntry.env.mkBEqCached lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkBEqCached_le_size rhsEntry.env lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .imp =>
        let ret := rhsEntry.env.mkImpCached lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkImpCached_le_size rhsEntry.env lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩


#eval ofBoolExprNatCached (.gate .and (.gate .and (.literal 0) (.literal 0)) (.gate .and (.literal 0) (.literal 0))) |>.env.decls

theorem ofBoolExprNatCached.go_decls_size_le (expr : BoolExprNat) (env : Env) :
    env.decls.size ≤ (ofBoolExprNatCached.go expr env).val.env.decls.size := by
  exact (ofBoolExprNatCached.go expr env).property

theorem ofBoolExprNatCached.go_decl_eq (idx) (env) (h : idx < env.decls.size) (hbounds) :
    (ofBoolExprNatCached.go expr env).val.env.decls[idx]'hbounds = env.decls[idx] := by
  induction expr generalizing env with
  | const =>
    simp only [go]
    apply mkConstCached_decl_eq
  | literal =>
    simp only [go]
    apply mkAtomCached_decl_eq
  | not expr ih =>
    simp only [go]
    have := go_decls_size_le expr env
    specialize ih env (by omega) (by omega)
    rw [mkNotCached_decl_eq]
    assumption
  | gate g lhs rhs lih rih =>
    have := go_decls_size_le lhs env
    have := go_decls_size_le rhs (go lhs env).val.env
    specialize lih env (by omega) (by omega)
    specialize rih (go lhs env).val.env (by omega) (by omega)
    cases g with
    | and =>
      simp only [go]
      rw [mkAndCached_decl_eq]
      rw [rih, lih]
    | or =>
      simp only [go]
      rw [mkOrCached_decl_eq]
      rw [rih, lih]
    | xor =>
      simp only [go]
      rw [mkXorCached_decl_eq]
      rw [rih, lih]
    | beq =>
      simp only [go]
      rw [mkBEqCached_decl_eq]
      rw [rih, lih]
    | imp =>
      simp only [go]
      rw [mkImpCached_decl_eq]
      rw [rih, lih]

theorem ofBoolExprNatCached.go_IsPrefix_env : IsPrefix env.decls (go expr env).val.env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply ofBoolExprNatCached.go_decl_eq
  . apply ofBoolExprNatCached.go_decls_size_le

@[simp]
theorem ofBoolExprNatCached.go_denote_entry (entry : Entrypoint) {h}:
    ⟦(go expr entry.env).val.env, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ := by
  apply denote.eq_of_env_eq
  apply ofBoolExprNatCached.go_IsPrefix_env

theorem ofBoolExprNatCached.go_eval_eq_ofBoolExprgo_eval (expr : BoolExprNat) (assign : List Bool) (env : Env) :
    ⟦(ofBoolExprNatCached.go expr env).val, assign⟧
      =
    ⟦(ofBoolExprNat.go expr env).val, assign⟧ := by
  induction expr generalizing env with
  | const =>
    dsimp [go]
    simp
  | literal =>
    dsimp [go]
    simp
  | not expr ih =>
    dsimp [go]
    simp [ih]
  | gate g lhs rhs lih rih =>
    cases g with
    | and =>
      dsimp [go]
      simp [Gate.eval, rih, lih]
    | or =>
      dsimp [go]
      simp only [ofBoolExprNat.go_eval_eq_eval, BoolExprNat.eval_gate, Gate.eval]
      simp [rih, lih]
    | xor =>
      dsimp [go]
      simp only [ofBoolExprNat.go_eval_eq_eval, BoolExprNat.eval_gate, Gate.eval]
      simp [rih, lih]
    | beq =>
      dsimp [go]
      simp only [ofBoolExprNat.go_eval_eq_eval, BoolExprNat.eval_gate, Gate.eval]
      simp [rih, lih]
    | imp =>
      dsimp [go]
      simp only [ofBoolExprNat.go_eval_eq_eval, BoolExprNat.eval_gate, Gate.eval]
      simp [rih, lih]

theorem ofBoolExprNatCached_eval_eq_ofBoolExpr_eval (expr : BoolExprNat) (assign : List Bool) :
    ⟦ofBoolExprNatCached expr, assign⟧ = ⟦ofBoolExprNat expr, assign⟧ := by
  unfold ofBoolExprNatCached
  rw [ofBoolExprNatCached.go_eval_eq_ofBoolExprgo_eval]
  unfold ofBoolExprNat
  rfl

@[simp]
theorem ofBoolExprCached_eval_eq_eval (expr : BoolExprNat) (assign : List Bool) :
    ⟦ofBoolExprNatCached expr, assign⟧ = expr.eval assign := by
  simp [ofBoolExprNatCached_eval_eq_ofBoolExpr_eval]

end Env
