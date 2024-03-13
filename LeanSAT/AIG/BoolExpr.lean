import LeanSAT.AIG.Basic
import LeanSAT.AIG.Lemmas

theorem or_as_and (a b : Bool) : (!(!a && !b)) = (a || b) := by cases a <;> cases b <;> decide
theorem xor_as_and (a b : Bool) : (!(a && b) && !(!a && !b)) = (xor a b) := by cases a <;> cases b <;> decide
theorem beq_as_and (a b : Bool) : (!(a && !b) && !(!a && b)) = (a == b) := by cases a <;> cases b <;> decide
theorem imp_as_and (a b : Bool) : (!(a && !b)) = (!a || b) := by cases a <;> cases b <;> decide

/--
Turn a `BoolExprNat` into an AIG + entrypoint. Note that this version is only meant
for proving purposes. For programming use `Env.ofBoolExprNatCached` and equality theorems.
-/
def Env.ofBoolExprNat (expr : BoolExprNat) : Env.Entrypoint :=
  go expr Env.empty |>.val
where
  /--
  This function contains a series of `have` statements that fulfill no obvious purpose.
  They are used to prove the `env.decls.size ≤ entry.env.decls.size` invariant of the return
  value with the final omega call in each case. This invariant is necessary as we recursively
  call this function multiple times so we need to guarantee that no recursive call ever shrinks
  the AIG in order to be allowed to use the generated AIG nodes.
  -/
  go (expr : BoolExprNat) (env : Env) : { entry : Env.Entrypoint // env.decls.size ≤ entry.env.decls.size } :=
    match expr with
    | .literal var => ⟨env.mkAtom var, (by apply Env.mkAtom_le_size)⟩
    | .const val => ⟨env.mkConst val, (by apply Env.mkConst_le_size)⟩
    | .not expr =>
      -- ¬x = true && invert x
      let ⟨exprEntry, _⟩ := go expr env
      let constEntry := exprEntry.env.mkConst true
      have := exprEntry.env.mkConst_le_size true
      let ret :=
       constEntry.env.mkGate
         constEntry.start
         exprEntry.start
         false
         true
         constEntry.inv
         (by apply Env.lt_mkConst_size)
      have := constEntry.env.mkGate_le_size _ _ false true constEntry.inv (by apply Env.lt_mkConst_size)
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
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            false
            false
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ false false h1 rhsEntry.inv
        ⟨ret, by dsimp [ret] at *; omega⟩
      | .or =>
        -- x or y = true && (invert (invert x && invert y))
        let auxEntry :=
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            true
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ true true h1 rhsEntry.inv
        let constEntry := auxEntry.env.mkConst true
        have := auxEntry.env.mkConst_le_size true
        let ret :=
          constEntry.env.mkGate
            constEntry.start
            auxEntry.start
            false
            true
            constEntry.inv
            (by apply Env.lt_mkConst_size)
        have := constEntry.env.mkGate_le_size _ auxEntry.start false true constEntry.inv (by apply Env.lt_mkConst_size)
        ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩
      | .xor =>
        -- x xor y = (invert (invert (x && y))) && (invert ((invert x) && (invert y)))
        let aux1Entry :=
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            false
            false
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ false false h1 rhsEntry.inv
        have h3 : lhsEntry.start < aux1Entry.env.decls.size := by
          dsimp [aux1Entry] at *
          omega
        let aux2Entry :=
          aux1Entry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            true
            true
            h3
            (by apply Env.lt_mkGate_size)
        have := aux1Entry.env.mkGate_le_size _ _ true true h3 (by apply Env.lt_mkGate_size)
        let ret :=
          aux2Entry.env.mkGate
            aux1Entry.start
            aux2Entry.start
            true
            true
            (by apply Env.lt_mkGate_size)
            aux2Entry.inv
        have := aux2Entry.env.mkGate_le_size aux1Entry.start _ true true (by apply Env.lt_mkGate_size) aux2Entry.inv
        ⟨ret, by simp (config := { zetaDelta := true}) only at *; omega⟩
      | .beq =>
        -- a == b = (invert (a && (invert b))) && (invert ((invert a) && b))
        let aux1Entry :=
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            false
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ false true h1 rhsEntry.inv
        have h3 : lhsEntry.start < aux1Entry.env.decls.size := by
          dsimp [aux1Entry] at *
          omega
        let aux2Entry :=
          aux1Entry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            true
            false
            h3
            (by apply Env.lt_mkGate_size)
        have := aux1Entry.env.mkGate_le_size _ _ true false h3 (by apply Env.lt_mkGate_size)
        let ret :=
          aux2Entry.env.mkGate
            aux1Entry.start
            aux2Entry.start
            true
            true
            (by apply Env.lt_mkGate_size)
            aux2Entry.inv
        have := aux2Entry.env.mkGate_le_size aux1Entry.start _ true true (by apply Env.lt_mkGate_size) aux2Entry.inv
        ⟨ret, by simp (config := { zetaDelta := true}) only at *; omega⟩
      | .imp =>
        -- a -> b = true && (invert (a and (invert b)))
        let auxEntry :=
          rhsEntry.env.mkGate
            lhsEntry.start
            rhsEntry.start
            false
            true
            h1
            rhsEntry.inv
        have := rhsEntry.env.mkGate_le_size _ _ false true h1 rhsEntry.inv
        let constEntry := mkConst true auxEntry.env
        have := auxEntry.env.mkConst_le_size true
        let ret :=
          constEntry.env.mkGate
            constEntry.start
            auxEntry.start
            false
            true
            constEntry.inv
            (by apply Env.lt_mkConst_size)
        have := constEntry.env.mkGate_le_size _ auxEntry.start false true constEntry.inv (by apply Env.lt_mkConst_size)
        ⟨ret, by dsimp [auxEntry, constEntry, ret] at *; omega⟩


#eval Env.ofBoolExprNat (.gate .and (.gate .and (.literal 0) (.literal 0)) (.gate .and (.literal 0) (.literal 0))) |>.env.decls

theorem Env.ofBoolExprNat.go_decls_size_le (expr : BoolExprNat) (env : Env) :
    env.decls.size ≤ (ofBoolExprNat.go expr env).val.env.decls.size := by
  exact (ofBoolExprNat.go expr env).property

theorem Env.ofBoolExprNat.go_decl_eq (idx) (env) (h : idx < env.decls.size) (hbounds) :
    (ofBoolExprNat.go expr env).val.env.decls[idx]'hbounds = env.decls[idx] := by
  induction expr generalizing env with
  | const =>
    simp only [go]
    apply Env.mkConst_decl_eq
  | literal =>
    simp only [go]
    apply Env.mkAtom_decl_eq
  | not expr ih =>
    simp only [go]
    have := go_decls_size_le expr env
    specialize ih env (by omega) (by omega)
    -- TODO: I think I want a more general theorem here
    simp [mkConst, mkAtom, mkGate, Array.push_get]
    split
    . split
      . assumption
      . omega
    . omega
  | gate g lhs rhs lih rih =>
    have := go_decls_size_le lhs env
    have := go_decls_size_le rhs (go lhs env).val.env
    specialize lih env (by omega) (by omega)
    specialize rih (go lhs env).val.env (by omega) (by omega)
    cases g with
    | and =>
      -- TODO: other use case for simp lemma
      simp only [go]
      simp [mkGate, mkAtom, Array.push_get]
      split
      . simp [rih, lih]
      . omega
    | or =>
      -- TODO: other use case for simp lemma
      simp only [go]
      simp [mkGate, mkAtom, mkConst, Array.push_get]
      split
      . split
        . split
          . simp [lih, rih]
          . omega
        . omega
      . omega
    | xor =>
      -- TODO: other use case for simp lemma
      simp only [go]
      simp [mkGate, mkAtom, Array.push_get]
      split
      . split
        . split
          . simp [lih, rih]
          . omega
        . omega
      . omega
    | beq =>
      -- TODO: other use case for simp lemma
      simp only [go]
      simp [mkGate, mkAtom, Array.push_get]
      split
      . split
        . split
          . simp [lih, rih]
          . omega
        . omega
      . omega
    | imp =>
      -- TODO: other use case for simp lemma
      simp only [go]
      simp [mkGate, mkAtom, mkConst, Array.push_get]
      split
      . split
        . split
          . simp [lih, rih]
          . omega
        . omega
      . omega

@[simp]
theorem Env.foo (entry : Entrypoint) {h}:
    denote ⟨(ofBoolExprNat.go expr entry.env).val.env, entry.start, h⟩ assign
      =
    denote entry assign := by
  apply Env.denote.eq_of_env_eq
  apply IsPrefix.of
  . intro idx h
    apply Env.ofBoolExprNat.go_decl_eq
  . apply Env.ofBoolExprNat.go_decls_size_le

theorem Env.ofBoolExprNatgo_eval_eq_eval (expr : BoolExprNat) (env : Env) (assign : List Bool) :
    denote (Env.ofBoolExprNat.go expr env) assign = expr.eval assign := by
  induction expr generalizing env with
  | const => simp [ofBoolExprNat.go]
  | literal => simp [ofBoolExprNat.go]
  | not expr ih =>
    simp [ofBoolExprNat.go]
    rw [← ih]
  | gate g lhs rhs lih rih =>
    cases g with
    | and =>
      simp [ofBoolExprNat.go, Gate.eval, lih, rih]
    | or =>
      simp [ofBoolExprNat.go, Gate.eval]
      rw [← or_as_and]
      simp [lih, rih]
    | xor =>
      simp [ofBoolExprNat.go, Gate.eval]
      rw [← xor_as_and]
      simp [lih, rih]
    | beq =>
      simp [ofBoolExprNat.go, Gate.eval]
      rw [← beq_as_and]
      simp [lih, rih]
    | imp =>
      simp [ofBoolExprNat.go, Gate.eval]
      rw [← imp_as_and]
      simp [lih, rih]

theorem Env.ofBoolExprNat_eval_eq_eval (expr : BoolExprNat) (assign : List Bool) :
    denote (Env.ofBoolExprNat expr) assign = expr.eval assign := by
  apply Env.ofBoolExprNatgo_eval_eq_eval
