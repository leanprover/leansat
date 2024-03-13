import LeanSAT.AIG.Cached
import LeanSAT.AIG.CachedLemmas
import LeanSAT.AIG.BoolExpr

-- lines such as: ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩
-- are slow because of the high defeq degree
-- TODO: ask leo how to fix this stuff
set_option pp.oneline true in
set_option trace.profiler true in
/--
Turn a `BoolExprNat` into an AIG + entrypoint. Note that this version is meant for programming
purposes. For proving use `Env.ofBoolExprNat` and equality theorems.
-/
def Env.ofBoolExprNatCached (expr : BoolExprNat) : Env.Entrypoint :=
  go expr Env.empty |>.val
where
  @[inherit_doc Env.ofBoolExprNat.go]
  go (expr : BoolExprNat) (env : Env) : { entry : Env.Entrypoint // env.decls.size ≤ entry.env.decls.size } :=
    match expr with
    | .literal var => ⟨env.mkAtomCached var, (by apply Env.mkAtomCached_le_size)⟩
    | .const val => ⟨env.mkConstCached val, (by apply Env.mkConstCached_le_size)⟩
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
         (by apply Env.lt_mkConstCached_size)
      have := constEntry.env.mkGateCached_le_size _ _ false true constEntry.inv (by apply Env.lt_mkConstCached_size)
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
            (by apply Env.lt_mkConstCached_size)
        have := constEntry.env.mkGateCached_le_size _ auxEntry.start false true constEntry.inv (by apply Env.lt_mkConstCached_size)
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
            (by apply Env.lt_mkGateCached_size)
        have := aux1Entry.env.mkGateCached_le_size _ _ true true h3 (by apply Env.lt_mkGateCached_size)
        let ret :=
          aux2Entry.env.mkGateCached
            aux1Entry.start
            aux2Entry.start
            true
            true
            (by apply Env.lt_mkGateCached_size)
            aux2Entry.inv
        have := aux2Entry.env.mkGateCached_le_size aux1Entry.start _ true true (by apply Env.lt_mkGateCached_size) aux2Entry.inv
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
            (by apply Env.lt_mkGateCached_size)
        have := aux1Entry.env.mkGateCached_le_size _ _ true false h3 (by apply Env.lt_mkGateCached_size)
        let ret :=
          aux2Entry.env.mkGateCached
            aux1Entry.start
            aux2Entry.start
            true
            true
            (by apply Env.lt_mkGateCached_size)
            aux2Entry.inv
        have := aux2Entry.env.mkGateCached_le_size aux1Entry.start _ true true (by apply Env.lt_mkGateCached_size) aux2Entry.inv
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
            (by apply Env.lt_mkConstCached_size)
        have := constEntry.env.mkGateCached_le_size _ auxEntry.start false true constEntry.inv (by apply Env.lt_mkConstCached_size)
        ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩

#eval Env.ofBoolExprNatCached (.gate .and (.gate .and (.literal 0) (.literal 0)) (.gate .and (.literal 0) (.literal 0))) |>.env.decls

theorem Env.ofBoolExprCachedgo_eval_eq_ofBoolExprgo_eval (expr : BoolExprNat) (assign : List Bool) (env : Env) :
    Env.denote (Env.ofBoolExprNatCached.go expr env).val assign = Env.denote (Env.ofBoolExprNat.go expr env).val assign := by
  sorry

theorem Env.ofBoolExprCached_eval_eq_ofBoolExpr_eval (expr : BoolExprNat) (assign : List Bool) :
    Env.denote (Env.ofBoolExprNatCached expr) assign = Env.denote (Env.ofBoolExprNat expr) assign := by
  unfold Env.ofBoolExprNatCached
  rw [Env.ofBoolExprCachedgo_eval_eq_ofBoolExprgo_eval]
  unfold Env.ofBoolExprNat
  rfl
