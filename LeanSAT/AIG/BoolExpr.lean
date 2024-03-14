import LeanSAT.AIG.Basic
import LeanSAT.AIG.Lemmas
import LeanSAT.AIG.Gates
import LeanSAT.AIG.GatesLemmas

namespace Env

/--
Turn a `BoolExprNat` into an AIG + entrypoint. Note that this version is only meant
for proving purposes. For programming use `Env.ofBoolExprNatCached` and equality theorems.
-/
def ofBoolExprNat (expr : BoolExprNat) : Entrypoint :=
  go expr Env.empty |>.val
where
  go (expr : BoolExprNat) (env : Env) : { entry : Entrypoint // env.decls.size ≤ entry.env.decls.size } :=
    match expr with
    | .literal var => ⟨env.mkAtom var, (by apply Env.mkAtom_le_size)⟩
    | .const val => ⟨env.mkConst val, (by apply Env.mkConst_le_size)⟩
    | .not expr =>
      let ⟨exprEntry, _⟩ := go expr env
      let ret := exprEntry.env.mkNot exprEntry.start exprEntry.inv
      have := mkNot_le_size exprEntry.env exprEntry.start exprEntry.inv
      ⟨ret, by dsimp [ret] at *; omega⟩
    | .gate g lhs rhs =>
      let ⟨lhsEntry, _⟩ := go lhs env
      let ⟨rhsEntry, _⟩ := go rhs lhsEntry.env
      have h1 : lhsEntry.start < Array.size rhsEntry.env.decls := by
        have := lhsEntry.inv
        omega
      match g with
      | .and =>
        let ret := rhsEntry.env.mkAnd lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkAnd_le_size rhsEntry.env lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .or =>
        let ret := rhsEntry.env.mkOr lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkOr_le_size rhsEntry.env lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .xor =>
        let ret := rhsEntry.env.mkXor lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkXor_le_size rhsEntry.env lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .beq =>
        let ret := rhsEntry.env.mkBEq lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkBEq_le_size rhsEntry.env lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .imp =>
        let ret := rhsEntry.env.mkImp lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        have := mkImp_le_size rhsEntry.env lhsEntry.start rhsEntry.start h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩


#eval ofBoolExprNat (.gate .and (.gate .and (.literal 0) (.literal 0)) (.gate .and (.literal 0) (.literal 0))) |>.env.decls

theorem ofBoolExprNat.go_decls_size_le (expr : BoolExprNat) (env : Env) :
    env.decls.size ≤ (ofBoolExprNat.go expr env).val.env.decls.size := by
  exact (ofBoolExprNat.go expr env).property

theorem ofBoolExprNat.go_decl_eq (idx) (env) (h : idx < env.decls.size) (hbounds) :
    (ofBoolExprNat.go expr env).val.env.decls[idx]'hbounds = env.decls[idx] := by
  induction expr generalizing env with
  | const =>
    simp only [go]
    apply mkConst_decl_eq
  | literal =>
    simp only [go]
    apply mkAtom_decl_eq
  | not expr ih =>
    have := go_decls_size_le expr env
    specialize ih env (by omega) (by omega)
    simp [go, ih]
    rw [mkNot_decl_eq]
    assumption
  | gate g lhs rhs lih rih =>
    have := go_decls_size_le lhs env
    have := go_decls_size_le rhs (go lhs env).val.env
    specialize lih env (by omega) (by omega)
    specialize rih (go lhs env).val.env (by omega) (by omega)
    cases g with
    | and =>
      simp [go]
      rw [mkAnd_decl_eq]
      rw [rih, lih]
    | or =>
      simp [go]
      rw [mkOr_decl_eq]
      rw [rih, lih]
    | xor =>
      simp [go]
      rw [mkXor_decl_eq]
      rw [rih, lih]
    | beq =>
      simp [go]
      rw [mkBEq_decl_eq]
      rw [rih, lih]
    | imp =>
      simp [go]
      rw [mkImp_decl_eq]
      rw [rih, lih]

theorem ofBoolExprNat.go_IsPrefix_env : IsPrefix env.decls (go expr env).val.env.decls := by
  apply IsPrefix.of
  . intro idx h
    apply ofBoolExprNat.go_decl_eq
  . apply ofBoolExprNat.go_decls_size_le

@[simp]
theorem ofBoolExprNat.go_denote_entry (entry : Entrypoint) {h}:
    ⟦(go expr entry.env).val.env, ⟨entry.start, h⟩, assign ⟧
      =
    ⟦entry, assign⟧ := by
  apply denote.eq_of_env_eq
  apply ofBoolExprNat.go_IsPrefix_env

@[simp]
theorem ofBoolExprNat.go_eval_eq_eval (expr : BoolExprNat) (env : Env) (assign : List Bool) :
    ⟦go expr env, assign⟧ = expr.eval assign := by
  induction expr generalizing env with
  | const => simp [go]
  | literal => simp [go]
  | not expr ih => simp [go, ih]
  | gate g lhs rhs lih rih => cases g <;> simp [go, Gate.eval, lih, rih]

@[simp]
theorem ofBoolExprNat.eval_eq_eval (expr : BoolExprNat) (assign : List Bool) :
    ⟦ofBoolExprNat expr, assign⟧ = expr.eval assign := by
  apply ofBoolExprNat.go_eval_eq_eval

end Env
