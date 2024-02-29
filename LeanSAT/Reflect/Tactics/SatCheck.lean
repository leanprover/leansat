import LeanSAT.Reflect.Tactics.SatDecide

open Lean Elab Meta ReflectSat

namespace SatCheck

structure TacticContext extends SatDecide.TacticContext where
  lratPath : System.FilePath

def TacticContext.new (lratPath : System.FilePath) : TermElabM TacticContext := do
  let inner ← SatDecide.TacticContext.new
  let ctx ← readThe Lean.Core.Context
  let srcPath := System.FilePath.mk ctx.fileName
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of '{srcPath}'"
  let lratPath := srcDir / lratPath
  return TacticContext.mk inner lratPath

/--
Prepare an `Expr` that proofs `boolExpr.unsat` using `ofReduceBool`.
-/
def lratChecker (cfg : TacticContext) (boolExpr : BoolExprNat) : MetaM Expr := do
  let cert ← SatDecide.LratCert.ofFile cfg.lratPath
  cert.toReflectionProof cfg.toTacticContext boolExpr

/--
Close a goal by:
1. Turning it into a SAT problem.
2. Parsing a previously produced LRAT proof for that SAT problem.
3. Verifying the LRAT proof using proof by reflection.
-/
def _root_.Lean.MVarId.satCheck (g : MVarId) (cfg : TacticContext) : MetaM Unit := do
  let unsatProver (exp : BoolExprNat) : MetaM Expr := do
    withTraceNode `sat (fun _ => return "Preparing LRAT reflection term") do
      lratChecker cfg exp
  g.closeWithBoolReflection unsatProver

@[inherit_doc Lean.MVarId.satCheck]
syntax (name := satCheckSyntax) "sat_check" str : tactic

end SatCheck

open Elab.Tactic
elab_rules : tactic
  | `(tactic| sat_check $path:str) => do
    let cfg ← SatCheck.TacticContext.new path.getString
    liftMetaFinishingTactic fun g => g.satCheck cfg
