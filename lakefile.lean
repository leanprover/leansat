import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4.git"@"20a48c9c02e135138d8281c50f772269d78eb1fc"

package LeanSAT {
  precompileModules := true
  -- This is 32 MB stack size for threads, we need this for bitblasting very large formulas
  moreGlobalServerArgs := #["--tstack=32000"]
}

lean_lib Test

@[default_target]
lean_lib LeanSAT

@[default_target]
lean_exe defaultExe {
  root := `Main
}
