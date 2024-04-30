import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4.git"@"d90cfcd9cb889f7ea4d335026d869ee4c990f21e"

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
