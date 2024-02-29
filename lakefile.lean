import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4.git"@"List.ofFn"

package LeanSAT {
  precompileModules := true
}

lean_lib Test

@[default_target]
lean_lib LeanSAT

@[default_target]
lean_exe defaultExe {
  root := `Main
}
