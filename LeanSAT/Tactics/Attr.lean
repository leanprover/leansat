/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Util.Trace
import Lean.Elab.Tactic.Simp

open Lean

initialize registerTraceClass `sat
initialize registerTraceClass `bv

register_option sat.solver : String := {
  defValue := "cadical"
  descr := "name of the SAT solver used by LeanSAT tactics"
}

register_option sat.prevalidate : Bool := {
  defValue := false
  descr := "Parse the LRAT proof before passing it into the kernel. Useful debugging."
}

register_option sat.timeout : Nat := {
  defValue := 10
  descr := "the number of seconds that the sat solver is run before aborting"
}

register_option bv.graphviz : Bool := {
  defValue := false
  descr := "Output the AIG as graphviz file when using the bv_decide tactic"
}

register_option bv.trimProofs : Bool := {
  defValue := true
  descr := "Whether to run the trimming algorithm on LRAT proofs"
}

initialize bvNormalizeExt : Meta.SimpExtension ←
  Meta.registerSimpAttr `bv_normalize "simp theorems used by bv_normalize"

initialize bvNormalizeSimprocExt : Meta.Simp.SimprocExtension ←
  Meta.Simp.registerSimprocAttr `bv_normalize_proc "simprocs used by bv_normalize" none
