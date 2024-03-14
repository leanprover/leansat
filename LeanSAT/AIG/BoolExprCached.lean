import LeanSAT.AIG.Cached
import LeanSAT.AIG.CachedLemmas
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
  @[inherit_doc Env.ofBoolExprNat.go]
  go (expr : BoolExprNat) (env : Env) : { entry : Entrypoint // env.decls.size ≤ entry.env.decls.size } :=
    match expr with
    | .literal var => ⟨env.mkAtomCached var, (by apply mkAtomCached_le_size)⟩
    | .const val => ⟨env.mkConstCached val, (by apply mkConstCached_le_size)⟩
    | .not expr =>
      -- ¬x = true && invert x
      let ⟨exprEntry, _⟩ := go expr env
      let constEntry := exprEntry.env.mkConstCached true
      have := exprEntry.env.mkConstCached_le_size true
      let ret :=
       constEntry.env.mkGateCached
         constEntry.start
         exprEntry.start
         false
         true
         constEntry.inv
         (by apply lt_mkConstCached_size)
      have := constEntry.env.mkGateCached_le_size _ _ false true constEntry.inv (by apply lt_mkConstCached_size)
      ⟨ret, by dsimp [constEntry, ret] at *; omega⟩
    | .gate g lhs rhs =>
      let ⟨lhsEntry, _⟩ := go lhs env
      let ⟨rhsEntry, _⟩ := go rhs lhsEntry.env
      have h1 : lhsEntry.start < Array.size rhsEntry.env.decls := by
        have := lhsEntry.inv
        omega
      match g with
      | .and =>
        let ret :=
          rhsEntry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            false
            false
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGateCached_le_size _ _ false false h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .or =>
        -- x or y = true && (invert (invert x && invert y))
        let auxEntry :=
          rhsEntry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            true
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGateCached_le_size _ _ true true h1 rhsEntry.inv
        let constEntry := auxEntry.env.mkConstCached true
        have := auxEntry.env.mkConstCached_le_size true
        let ret :=
          constEntry.env.mkGateCached
            constEntry.start
            auxEntry.start
            false
            true
            constEntry.inv
            (by apply lt_mkConstCached_size)
        have := constEntry.env.mkGateCached_le_size _ auxEntry.start false true constEntry.inv (by apply lt_mkConstCached_size)
        ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩
      | .xor =>
        -- x xor y = (invert (invert (x && y))) && (invert ((invert x) && (invert y)))
        let aux1Entry :=
          rhsEntry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            false
            false
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGateCached_le_size _ _ false false h1 rhsEntry.inv
        have h3 : lhsEntry.start < aux1Entry.env.decls.size := by
          dsimp [aux1Entry] at *
          omega
        let aux2Entry :=
          aux1Entry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            true
            true
            h3
            (by apply lt_mkGateCached_size)
        have := aux1Entry.env.mkGateCached_le_size _ _ true true h3 (by apply lt_mkGateCached_size)
        let ret :=
          aux2Entry.env.mkGateCached
            aux1Entry.start
            aux2Entry.start
            true
            true
            (by apply lt_mkGateCached_size)
            aux2Entry.inv
        have := aux2Entry.env.mkGateCached_le_size aux1Entry.start _ true true (by apply lt_mkGateCached_size) aux2Entry.inv
        ⟨ret, by simp (config := { zetaDelta := true}) only at *; omega⟩
      | .beq =>
        -- a == b = (invert (a && (invert b))) && (invert ((invert a) && b))
        let aux1Entry :=
          rhsEntry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            false
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGateCached_le_size _ _ false true h1 rhsEntry.inv
        have h3 : lhsEntry.start < aux1Entry.env.decls.size := by
          dsimp [aux1Entry] at *
          omega
        let aux2Entry :=
          aux1Entry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            true
            false
            h3
            (by apply lt_mkGateCached_size)
        have := aux1Entry.env.mkGateCached_le_size _ _ true false h3 (by apply lt_mkGateCached_size)
        let ret :=
          aux2Entry.env.mkGateCached
            aux1Entry.start
            aux2Entry.start
            true
            true
            (by apply lt_mkGateCached_size)
            aux2Entry.inv
        have := aux2Entry.env.mkGateCached_le_size aux1Entry.start _ true true (by apply lt_mkGateCached_size) aux2Entry.inv
        ⟨ret, by simp (config := { zetaDelta := true}) only at *; omega⟩
      | .imp =>
        -- a -> b = true && (invert (a and (invert b)))
        let auxEntry :=
          rhsEntry.env.mkGateCached
            lhsEntry.start
            rhsEntry.start
            false
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGateCached_le_size _ _ false true h1 rhsEntry.inv
        let constEntry := mkConstCached true auxEntry.env
        have := auxEntry.env.mkConstCached_le_size true
        let ret :=
          constEntry.env.mkGateCached
            constEntry.start
            auxEntry.start
            false
            true
            constEntry.inv
            (by apply lt_mkConstCached_size)
        have := constEntry.env.mkGateCached_le_size _ auxEntry.start false true constEntry.inv (by apply lt_mkConstCached_size)
        ⟨ret, by simp [auxEntry, constEntry, ret] at *; omega⟩


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
    rw [mkGateCached_decl_eq]
    rw [mkConstCached_decl_eq]
    . rw [ih]
    . have := mkConstCached_le_size (go expr env).val.env true
      omega
  | gate g lhs rhs lih rih =>
    have := go_decls_size_le lhs env
    have := go_decls_size_le rhs (go lhs env).val.env
    specialize lih env (by omega) (by omega)
    specialize rih (go lhs env).val.env (by omega) (by omega)
    cases g with
    | and =>
      simp only [go]
      rw [mkGateCached_decl_eq]
      rw [rih, lih]
    | or =>
      simp only [go]
      rw [mkGateCached_decl_eq, mkConstCached_decl_eq, mkGateCached_decl_eq]
      . rw [rih, lih]
      . apply lt_mkGateCached_size_of_lt_env_size
        omega
      . apply lt_mkConstCached_size_of_lt_env_size
        apply lt_mkGateCached_size_of_lt_env_size
        omega
    | xor =>
      simp only [go]
      rw [mkGateCached_decl_eq, mkGateCached_decl_eq, mkGateCached_decl_eq]
      rw [rih, lih]
      . apply lt_mkGateCached_size_of_lt_env_size
        omega
      . apply lt_mkGateCached_size_of_lt_env_size
        apply lt_mkGateCached_size_of_lt_env_size
        omega
    | beq =>
      simp only [go]
      rw [mkGateCached_decl_eq, mkGateCached_decl_eq, mkGateCached_decl_eq]
      rw [rih, lih]
      . apply lt_mkGateCached_size_of_lt_env_size
        omega
      . apply lt_mkGateCached_size_of_lt_env_size
        apply lt_mkGateCached_size_of_lt_env_size
        omega
    | imp =>
      simp only [go]
      rw [mkGateCached_decl_eq, mkConstCached_decl_eq, mkGateCached_decl_eq]
      rw [rih, lih]
      . apply lt_mkGateCached_size_of_lt_env_size
        omega
      . apply lt_mkConstCached_size_of_lt_env_size
        apply lt_mkGateCached_size_of_lt_env_size
        omega

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
      rw [← or_as_and]
      simp [rih, lih]
    | xor =>
      dsimp [go]
      simp only [ofBoolExprNat.go_eval_eq_eval, BoolExprNat.eval_gate, Gate.eval]
      rw [← xor_as_and]
      simp [rih, lih]
    | beq =>
      dsimp [go]
      simp only [ofBoolExprNat.go_eval_eq_eval, BoolExprNat.eval_gate, Gate.eval]
      rw [← beq_as_and]
      simp [rih, lih]
    | imp =>
      dsimp [go]
      simp only [ofBoolExprNat.go_eval_eq_eval, BoolExprNat.eval_gate, Gate.eval]
      rw [← imp_as_and]
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
