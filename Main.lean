import LeanSAT.External.Solver
import LeanSAT.LRAT.LRATChecker
import LeanSAT.LRAT.LRATCheckerSound
import LeanSAT.External.LRAT
import LeanSAT.Reflect.Tactics.SatDecide

open Dimacs LRAT

def main : List String → IO Unit := fun args => do
  let prfFile := args[0]!
  let t1 ← IO.monoMsNow
  let content ← SatDecide.readFileQuick prfFile
  let t2 ← IO.monoMsNow
  let some output := parseLRATProof content | throw <| .userError "failed to parse"
  let t3 ← IO.monoMsNow

  IO.println s!"Read in {t2 - t1}, parsed {output.size} in {t3 - t2}ms"
