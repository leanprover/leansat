/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LeanSAT.Reflect.Tactics.Reflect
import LeanSAT.Reflect.CNF.Decidable -- This import is not used directly, but without it the tactic fails.
import LeanSAT.Reflect.BoolExpr.Tseitin.Lemmas

import LeanSAT.LRAT.LRATChecker
import LeanSAT.LRAT.LRATCheckerSound
import LeanSAT.External.Solver

open Lean Elab Meta ReflectSat

structure TacticConfig where
  boolExprDef : Name
  certDef : Name
  reflectionDef : Name

/--
Interface for an external SAT solver with a verified certificate checker.

The type `α` representing the specific encoding of `CNF Nat` that the `Solver`
backend uses.

The type `β` representing the unsatisfiability certificate should have `ToExpr β`,
because we will need to embed the certificate in the generated proof.
-/
structure Solver (α : Type) (β : Type) where
  /-- Encode the generic `CNF Nat` into the `Solver` specific CNF format. -/
  encodeCNF : CNF Nat → α
  /-- An IO function that retrieves an opaque certificate of type `β`. -/
  runExternal : α → IO β
  /--
  A verification function,
  where `verify (encodeCNF c) b = true` if `b` is a valid certificate of the unsatisfiability of `c`.
  -/
  verify : α → β → Bool
  /-- Proof of the correctness of the verification function. -/
  correct : ∀ c b, verify (encodeCNF c) b = true → c.unsat

def Solver.verifyExpr (s : Solver α β) (b : BoolExpr Nat) (c : β) : Bool :=
  s.verify (s.encodeCNF b.toCNF) c

theorem Solver.unsat_of_verifyExpr_eq_true (s : Solver α β) (b : BoolExpr Nat) (c : β)
    (h : s.verifyExpr b c = true) : BoolExpr.unsat b := by
  apply BoolExpr.unsat_of_toCNF_unsat
  apply s.correct
  rw [verifyExpr] at h
  exact h

def mkAuxDecl (name : Name) (value type : Expr) : MetaM Unit :=
  addAndCompile <| .defnDecl {
    name := name,
    levelParams := [],
    type := type,
    value := value,
    hints := .abbrev,
    safety := .safe
  }

/--
We can lift a `Solver β` to a function `CNF Nat → MetaM Expr`,
which given `x : CNF Nat` produces a proof of `x.unsat`.

But we need to jump through some hoops!
-/
def Solver.lift (cfg : TacticConfig) (solverName : Name) (cnfType : Expr) (certType : Expr)
    [ToExpr β] (s : Solver α β) (boolExpr : BoolExpr Nat) : MetaM Expr := do
  let cnf ←
    withTraceNode `sat (fun _ => return "Converting BoolExpr to CNF") do
      return boolExpr.toCNF
  trace[sat] "Converted to CNF: {cnf}"
  let encoded ←
    withTraceNode `sat (fun _ => return "Converting frontend CNF to solver specific CNF") do
      return s.encodeCNF cnf
  let cert ←
    withTraceNode `sat (fun _ => return "Obtaining external proof certificate") do
      s.runExternal encoded
  withTraceNode `sat (fun _ => return "Compiling BoolExpr term") do
    mkAuxDecl cfg.boolExprDef (toExpr boolExpr) (toTypeExpr (BoolExpr Nat))
  withTraceNode `sat (fun _ => return "Compiling proof certificate term") do
    mkAuxDecl cfg.certDef (toExpr cert) certType

  let boolExpr := mkConst cfg.boolExprDef
  let certExpr := mkConst cfg.certDef
  let solverExpr := mkConst solverName

  withTraceNode `sat (fun _ => return "Compiling reflection proof term") do
    let auxValue := mkApp5 (mkConst ``Solver.verifyExpr) cnfType certType solverExpr boolExpr certExpr
    mkAuxDecl cfg.reflectionDef auxValue (mkConst ``Bool)

  let nativeProof := mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst cfg.reflectionDef) (toExpr true) (← mkEqRefl (toExpr true))
  return mkApp6 (mkConst ``Solver.unsat_of_verifyExpr_eq_true) cnfType certType solverExpr boolExpr certExpr nativeProof

/--
A wrapper type for `LRAT.DefaultFormula`. We use it to hide the `numVars` parameter
as the `Solver` framework does not intend for dependent typing like this.
-/
structure LratFormula where
  /-- Number of variables in `formula`. -/
  numVars : Nat
  /-- The actual SAT formula in the LeanSAT framework. -/
  formula : LRAT.DefaultFormula numVars.succ

/--
An LRAT proof certificate. Note that this only contains a list of LRAT actions
that have not yet been internalized to the formats that LeanSAT's LRAT checker uses.
This is done as we need to provide an `ToExpr LratCert` instance, which not easily
possible for proof carrying structures.
-/
structure LratCert where
  /-- The list of LRAT actions to take for the proof. -/
  cert : List LRAT.IntAction

instance : ToExpr LRAT.IntAction where
  toExpr action :=
    let beta := mkApp (mkConst ``Array [.zero]) (mkConst ``Int)
    let alpha := mkConst ``Nat
    match action with
    | .addEmpty id hints =>
      mkApp4 (mkConst ``LRAT.Action.addEmpty [.zero, .zero]) beta alpha (toExpr id) (toExpr hints)
    | .addRup id c hints =>
      mkApp5 (mkConst ``LRAT.Action.addRup [.zero, .zero]) beta alpha (toExpr id) (toExpr c) (toExpr hints)
    | .addRat id c pivot rupHints ratHints =>
      mkApp7 (mkConst ``LRAT.Action.addRat [.zero, .zero]) beta alpha (toExpr id) (toExpr c) (toExpr pivot) (toExpr rupHints) (toExpr ratHints)
    | .del ids =>
      mkApp3 (mkConst ``LRAT.Action.del [.zero, .zero]) beta alpha (toExpr ids)
  toTypeExpr := mkConst ``LRAT.IntAction

instance : ToExpr LratCert where
  toExpr cert := mkApp (mkConst ``LratCert.mk) (toExpr cert.cert)
  toTypeExpr := mkConst ``LratCert

def liftCnf (cnf : CNF Nat) : CNF (PosFin (cnf.numLiterals + 1)) :=
  let cnf := cnf.relabelFin
  cnf.relabel (fun lit => ⟨lit.val + 1, by omega⟩)

theorem unsat_of_liftCnf_unsat (cnf : CNF Nat) : CNF.unsat (liftCnf cnf) → CNF.unsat cnf := by
  intro h2
  have h3 :=
    CNF.unsat_relabel_iff
      (by
        intro a b ha hb hab
        injections hab
        cases a; cases b; simp_all)
      |>.mp h2
  have h4 := CNF.unsat_relabelFin.mp h3
  assumption

def convertClause (clause : CNF.Clause (PosFin n)) : Option (LRAT.DefaultClause n) :=
  LRAT.DefaultClause.ofArray clause.toArray

def convertClauses (clauses : CNF (PosFin n)) : List (Option (LRAT.DefaultClause n)) :=
  clauses.map convertClause

theorem mem_lratClause_of_mem_clause (clause : CNF.Clause (PosFin n)) (h1 : l ∈ clause)
    (h2 : LRAT.DefaultClause.ofArray clause.toArray = some lratClause) : l ∈ lratClause.clause := by
  induction clause generalizing lratClause with
  | nil => cases h1
  | cons hd tl ih =>
    unfold LRAT.DefaultClause.ofArray at h2
    rw [Array.foldr_eq_foldr_data,Array.toArray_data] at h2
    dsimp only [List.foldr] at h2
    split at h2
    · cases h2
    · rw [LRAT.DefaultClause.insert] at h2
      split at h2
      · cases h2
      · split at h2
        · rename_i h
          rw [<-Option.some.inj h2] at *
          cases h1
          · exact List.mem_of_elem_eq_true h
          · apply ih
            · assumption
            · next heq _ _ =>
              unfold LRAT.DefaultClause.ofArray
              rw [Array.foldr_eq_foldr_data,Array.toArray_data]
              exact heq
        · cases h1
          · simp only [<-Option.some.inj h2]
            constructor
          · simp only at h2
            simp only [<-Option.some.inj h2]
            rename_i heq _ _ _
            apply List.Mem.tail
            apply ih
            assumption
            unfold LRAT.DefaultClause.ofArray
            rw [Array.foldr_eq_foldr_data,Array.toArray_data]
            exact heq

theorem convertClause_sat_of_cnf_sat (clause : CNF.Clause (PosFin n)) (h : convertClause clause = some lratClause) :
    CNF.Clause.eval assign clause → assign ⊨ lratClause := by
  intro h2
  simp only [CNF.Clause.eval, List.any_eq_true, bne_iff_ne, ne_eq] at h2
  simp only [HSat.eval, List.any_eq_true, decide_eq_true_eq]
  rcases h2 with ⟨lit, ⟨hlit1, hlit2⟩⟩
  apply Exists.intro (lit.fst, lit.snd)
  constructor
  . simp[LRAT.Clause.toList, LRAT.DefaultClause.toList]
    simp[convertClause] at h
    exact mem_lratClause_of_mem_clause clause hlit1 h
  . simp_all

/--
Convert a `CNF Nat` with a certain maximum variable number into the `LRAT.DefaultFormula`
format for usage with LeanSAT.

Notably this:
1. Increments all variables as DIMACS variables start at 1 instead of 0
2. Adds a leading `none` clause. This clause *must* be persistet as the LRAT proof
   refers to the DIMACS file line by line and the DIMACS file begins with the
  `p cnf x y` meta instruction.
-/
def convertCNF (cnf : CNF Nat) : LRAT.DefaultFormula (cnf.numLiterals + 1) :=
  let lifted := liftCnf cnf
  let lratCnf := convertClauses lifted
  LRAT.DefaultFormula.ofArray (none :: lratCnf).toArray


theorem convertCNF_readfyForRupAdd : LRAT.DefaultFormula.readyForRupAdd (convertCNF cnf) := by
  unfold convertCNF
  apply LRAT.DefaultFormula.ofArray_readyForRupAdd

theorem convertCNF_readfyForRatAdd : LRAT.DefaultFormula.readyForRatAdd (convertCNF cnf) := by
  unfold convertCNF
  apply LRAT.DefaultFormula.ofArray_readyForRatAdd

theorem unsat_of_cons_none_unsat (clauses : List (Option (LRAT.DefaultClause n))) :
    unsatisfiable (PosFin n) (LRAT.DefaultFormula.ofArray (none :: clauses).toArray)
      →
    unsatisfiable (PosFin n) (LRAT.DefaultFormula.ofArray clauses.toArray) := by
  intro h assign hassign
  apply h assign
  simp only [LRAT.Formula.formulaHSat_def, List.all_eq_true, decide_eq_true_eq] at *
  intro clause hclause
  simp_all[LRAT.DefaultFormula.ofArray, LRAT.Formula.toList, LRAT.DefaultFormula.toList]

def mkTemp : IO System.FilePath := do
  let out ← IO.Process.output { cmd := "mktemp" }
  return out.stdout.trim

def lratSolver : Solver LratFormula LratCert where
  encodeCNF reflectCnf :=
    ⟨_, convertCNF reflectCnf⟩

  runExternal formula := do
    let formula := formula.formula
    -- TODO: In the future we might want to cache these
    let cnfPath ← mkTemp
    let lratPath ← mkTemp
    IO.FS.writeFile cnfPath <| formula.dimacs
    -- TODO: make cadical parameterizable
    satQuery "cadical" cnfPath lratPath
    let some lratProof ← LRAT.parseLRATProof lratPath.toString | throw <| IO.userError "SAT solver produced invalid LRAT"
    -- cleanup files such that we don't pollute /tmp
    IO.FS.removeFile cnfPath
    IO.FS.removeFile lratPath
    return ⟨lratProof.toList⟩

  verify formula cert :=
    let lratProof := cert.cert.map (LRAT.intActionToDefaultClauseAction formula.numVars.succ)
    let lratProof : List { act // LRAT.wellFormedAction act } :=
      lratProof.filterMap
        (fun actOpt =>
          match actOpt with
          | none => none
          | some (LRAT.Action.addEmpty id rupHints) =>
            some ⟨LRAT.Action.addEmpty id rupHints, by simp only [LRAT.wellFormedAction]⟩
          | some (LRAT.Action.addRup id c rupHints) =>
            some ⟨LRAT.Action.addRup id c rupHints, by simp only [LRAT.wellFormedAction]⟩
          | some (LRAT.Action.del ids) =>
            some ⟨LRAT.Action.del ids, by simp only [LRAT.wellFormedAction]⟩
          | some (LRAT.Action.addRat id c pivot rupHints ratHints) =>
            if h : pivot ∈ LRAT.Clause.toList c then
              some ⟨
                LRAT.Action.addRat id c pivot rupHints ratHints,
                by simp [LRAT.wellFormedAction, LRAT.Clause.limplies_iff_mem, h]
              ⟩
            else
              -- TODO: report this
              none
        )
    let lratProof := lratProof.map Subtype.val
    let checkerResult := LRAT.lratChecker formula.formula lratProof
    checkerResult = .success

  correct := by
    intro c b h1
    simp only [decide_eq_true_eq] at h1
    have h2 :=
      lratCheckerSound
        _
        (by apply convertCNF_readfyForRupAdd)
        (by apply convertCNF_readfyForRatAdd)
        _
        (by
          intro action h
          simp only [List.mem_map, List.mem_filterMap] at h
          rcases h with ⟨wellFormedActions, _, h2⟩
          rw [← h2]
          exact wellFormedActions.property)
        h1
    apply unsat_of_liftCnf_unsat c
    intro assignment
    unfold convertCNF at h2
    have h2 := (unsat_of_cons_none_unsat _ h2) assignment
    apply eq_false_of_ne_true
    intro h3
    apply h2
    simp only [LRAT.Formula.formulaHSat_def, List.all_eq_true, decide_eq_true_eq]
    intro lratClause hlclause
    simp only [LRAT.Formula.toList, LRAT.DefaultFormula.toList, LRAT.DefaultFormula.ofArray,
      convertClauses, Array.size_toArray, List.length_map, Array.toList_eq, Array.data_toArray,
      List.map_nil, List.append_nil, List.mem_filterMap, List.mem_map, id_eq, exists_eq_right] at hlclause
    rcases hlclause with ⟨reflectClause, ⟨hrclause1, hrclause2⟩⟩
    simp only [CNF.eval, List.all_eq_true] at h3
    simp [convertClause_sat_of_cnf_sat reflectClause hrclause2, h3 reflectClause hrclause1]

def lratSolver' (cfg : TacticConfig) : BoolExpr Nat → MetaM Expr :=
  Solver.lift cfg ``lratSolver  (mkConst ``LratFormula) (mkConst ``LratCert) lratSolver

def _root_.Lean.MVarId.cnfDecide (g : MVarId) (cfg : TacticConfig) : MetaM Unit := M.run do
  let g' ← falseOrByContra g
  g'.withContext do
    let (boolExpr, f) ←
      withTraceNode `sat (fun _ => return "Reflecting goal into BoolExpr") do
        reflectSAT g'
    trace[sat] "Reflected boolean expression: {boolExpr}"
    let boolExprUnsat ←
      withTraceNode `sat (fun _ => return "Preparing LRAT reflection term") do
        lratSolver' cfg boolExpr
    IO.println "before proof construction"
    let proveFalse ← f boolExprUnsat
    IO.println "after proof construction"
    g'.assign proveFalse
    IO.println "after assign"

syntax (name := cnfDecideSyntax) "cnf_decide" : tactic

open Elab.Tactic
elab_rules : tactic
  | `(tactic| cnf_decide) => do
    let boolExprDef ← Term.mkAuxName `_boolExpr_def
    let certDef ← Term.mkAuxName `_cert_def
    let reflectionDef ← Term.mkAuxName `_reflection_def
    let cfg := { boolExprDef, certDef, reflectionDef }
    liftMetaFinishingTactic fun g => g.cnfDecide cfg
