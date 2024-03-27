import LeanSAT.AIG.BoolExprCached

def mkSharedTree (n : Nat) : BoolExpr Nat :=
  match n with
  | 0 => .literal 0
  | n + 1 =>
    let tree := mkSharedTree n
    .gate .and tree tree

/-- info: #[Decl.atom 0, Decl.gate 0 0 false false] -/
#guard_msgs in
#eval AIG.ofBoolExprCachedDirect (mkSharedTree 1) |>.aig.decls

/-- info: #[Decl.atom 0, Decl.gate 0 0 false false, Decl.gate 1 1 false false] -/
#guard_msgs in
#eval AIG.ofBoolExprCachedDirect (mkSharedTree 2) |>.aig.decls

/--
info: #[Decl.atom 0, Decl.gate 0 0 false false, Decl.gate 1 1 false false, Decl.gate 2 2 false false,
  Decl.gate 3 3 false false]
-/
#guard_msgs in
#eval AIG.ofBoolExprCachedDirect (mkSharedTree 4) |>.aig.decls

/--
info: #[Decl.atom 0, Decl.gate 0 0 false false, Decl.gate 1 1 false false, Decl.gate 2 2 false false,
  Decl.gate 3 3 false false, Decl.gate 4 4 false false, Decl.gate 5 5 false false, Decl.gate 6 6 false false,
  Decl.gate 7 7 false false, Decl.gate 8 8 false false, Decl.gate 9 9 false false, Decl.gate 10 10 false false,
  Decl.gate 11 11 false false, Decl.gate 12 12 false false, Decl.gate 13 13 false false, Decl.gate 14 14 false false,
  Decl.gate 15 15 false false]
-/
#guard_msgs in
#eval AIG.ofBoolExprCachedDirect (mkSharedTree 16) |>.aig.decls
