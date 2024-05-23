import LeanSAT.Reflect.Tactics.BVDecide
import LeanSAT.Reflect.Tactics.SatCheck

open Lean Elab Meta ReflectSat

namespace BVCheck

/--
Prepare an `Expr` that proofs `bvExpr.unsat` using `ofReduceBool`.
-/
def lratChecker (cfg : SatDecide.TacticContext) (bvExpr : BVLogicalExpr) : MetaM Expr := do
  let cert ← SatDecide.LratCert.ofFile cfg.lratPath cfg.prevalidate
  cert.toReflectionProof
    cfg
    bvExpr
    ``BVDecide.verifyBVExpr
    ``BVDecide.unsat_of_verifyBVExpr_eq_true

/--
Close a goal by:
1. Turning it into a BitVec problem.
2. Using bitblasting to turn that into a SAT problem.
3. Parsing a previously produced LRAT proof for that SAT problem.
4. Verifying the LRAT proof using proof by reflection.

It is called with the name of an LRAT file in the same directory as the current Lean file:
```
bv_check "proof.lrat"
```
-/
def _root_.Lean.MVarId.bvCheck (g : MVarId) (cfg : SatDecide.TacticContext) : MetaM Unit := do
  let unsatProver : BVDecide.UnsatProver := fun bvExpr _ => do
    withTraceNode `sat (fun _ => return "Preparing LRAT reflection term") do
      let proof ← lratChecker cfg bvExpr
      -- We just return a fake cert as nobody cares about it
      return ⟨proof, ""⟩
  let _ ← g.closeWithBVReflection unsatProver
  return ()

@[inherit_doc Lean.MVarId.bvCheck]
syntax (name := bvCheckSyntax) "bv_check " str : tactic

end BVCheck

open Elab.Tactic
elab_rules : tactic
  | `(tactic| bv_check $path:str) => do
    let cfg ← SatCheck.mkContext path.getString
    liftMetaFinishingTactic fun g => g.bvCheck cfg
