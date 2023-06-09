import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4.git"@"main"
require aesop from git "https://github.com/JLimperg/aesop"

package LeanSAT {
  precompileModules := true
}

lean_lib LeanSAT

@[default_target]
lean_exe defaultExe {
  root := `Main
}
