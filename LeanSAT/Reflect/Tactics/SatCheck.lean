import LeanSAT.Reflect.Tactics.SatDecide

open Lean Elab Meta ReflectSat

namespace SatCheck

/--
Get the directory that contains the Lean file which is currently being elaborated.
-/
def getSrcDir : TermElabM System.FilePath := do
  let ctx ← readThe Lean.Core.Context
  let srcPath := System.FilePath.mk ctx.fileName
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of '{srcPath}'"
  return srcDir

def mkContext (lratPath : System.FilePath) : TermElabM SatDecide.TacticContext := do
  let lratPath := (← getSrcDir) / lratPath
  SatDecide.TacticContext.new lratPath

/--
Prepare an `Expr` that proofs `boolExpr.unsat` using `ofReduceBool`.
-/
def lratChecker (cfg : SatDecide.TacticContext) (boolExpr : BoolExprNat) : MetaM Expr := do
  let cert ← SatDecide.LratCert.ofFile cfg.lratPath
  cert.toReflectionProof cfg boolExpr

/--
Close a goal by:
1. Turning it into a SAT problem.
2. Parsing a previously produced LRAT proof for that SAT problem.
3. Verifying the LRAT proof using proof by reflection.

It is called with the name of an LRAT file in the same directory as the current Lean file:
```
sat_check "proof.lrat"
```
-/
def _root_.Lean.MVarId.satCheck (g : MVarId) (cfg : SatDecide.TacticContext) : MetaM Unit := do
  let unsatProver (exp : BoolExprNat) : MetaM Expr := do
    withTraceNode `sat (fun _ => return "Preparing LRAT reflection term") do
      lratChecker cfg exp
  g.closeWithBoolReflection unsatProver

@[inherit_doc Lean.MVarId.satCheck]
syntax (name := satCheckSyntax) "sat_check " str : tactic

end SatCheck

open Elab.Tactic
elab_rules : tactic
  | `(tactic| sat_check $path:str) => do
    let cfg ← SatCheck.mkContext path.getString
    liftMetaFinishingTactic fun g => g.satCheck cfg
