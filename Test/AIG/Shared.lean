import LeanSAT.AIG.BoolExprCached

def mkSharedTree (n : Nat) : BoolExpr Nat :=
  match n with
  | 0 => .literal 0
  | n + 1 =>
    let tree := mkSharedTree n
    .gate .or tree tree

/-- info: #[Decl.atom 0, Decl.gate 0 0 true true, Decl.const true, Decl.gate 1 2 true false] -/
#guard_msgs in
#eval AIG.ofBoolExprCachedDirect (mkSharedTree 1) |>.aig.decls

/--
info: #[Decl.atom 0, Decl.gate 0 0 true true, Decl.const true, Decl.gate 1 2 true false, Decl.gate 3 3 true true,
  Decl.gate 2 4 false true]
-/
#guard_msgs in
#eval AIG.ofBoolExprCachedDirect (mkSharedTree 2) |>.aig.decls

/--
info: #[Decl.atom 0, Decl.gate 0 0 true true, Decl.const true, Decl.gate 1 2 true false, Decl.gate 3 3 true true,
  Decl.gate 2 4 false true, Decl.gate 5 5 true true, Decl.gate 2 6 false true, Decl.gate 7 7 true true,
  Decl.gate 2 8 false true]
-/
#guard_msgs in
#eval AIG.ofBoolExprCachedDirect (mkSharedTree 4) |>.aig.decls

/--
info: #[Decl.atom 0, Decl.gate 0 0 true true, Decl.const true, Decl.gate 1 2 true false, Decl.gate 3 3 true true,
  Decl.gate 2 4 false true, Decl.gate 5 5 true true, Decl.gate 2 6 false true, Decl.gate 7 7 true true,
  Decl.gate 2 8 false true, Decl.gate 9 9 true true, Decl.gate 2 10 false true, Decl.gate 11 11 true true,
  Decl.gate 2 12 false true, Decl.gate 13 13 true true, Decl.gate 2 14 false true, Decl.gate 15 15 true true,
  Decl.gate 2 16 false true, Decl.gate 17 17 true true, Decl.gate 2 18 false true, Decl.gate 19 19 true true,
  Decl.gate 2 20 false true, Decl.gate 21 21 true true, Decl.gate 2 22 false true, Decl.gate 23 23 true true,
  Decl.gate 2 24 false true, Decl.gate 25 25 true true, Decl.gate 2 26 false true, Decl.gate 27 27 true true,
  Decl.gate 2 28 false true, Decl.gate 29 29 true true, Decl.gate 2 30 false true, Decl.gate 31 31 true true,
  Decl.gate 2 32 false true]
-/
#guard_msgs in
#eval AIG.ofBoolExprCachedDirect (mkSharedTree 16) |>.aig.decls
