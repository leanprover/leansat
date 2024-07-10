import Lake
open Lake DSL

package LeanSAT {
  -- This is 32 MB stack size for threads, we need this for bitblasting very large formulas
  moreGlobalServerArgs := #["--tstack=32000"]
}

@[test_driver]
lean_lib Test

lean_lib Eval

@[default_target]
lean_lib LeanSAT {
  precompileModules := true
}

@[default_target]
lean_exe defaultExe {
  root := `Main
}
