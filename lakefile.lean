import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4.git"@"e0eb3090ec2e5044c92e9bba9c269c91375f8d5e"

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
