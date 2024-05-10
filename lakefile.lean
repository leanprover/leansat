import Lake
open Lake DSL

require batteries from git "https://github.com/leanprover-community/batteries.git"@"nightly-testing"

package LeanSAT {
  precompileModules := true
  -- This is 32 MB stack size for threads, we need this for bitblasting very large formulas
  moreGlobalServerArgs := #["--tstack=32000"]
}

lean_lib Test
lean_lib Eval

@[default_target]
lean_lib LeanSAT

@[default_target]
lean_exe defaultExe {
  root := `Main
}
