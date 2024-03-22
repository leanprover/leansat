import LeanSAT.AIG.BoolExprCached

def mkFalseCollapsible (n : Nat) : BoolExpr Nat :=
  match n with
  | 0 => .const false
  | n + 1 =>
    let tree := mkFalseCollapsible n
    .gate .and tree tree

/-- info: #[Decl.const false] -/
#guard_msgs in
#eval AIG.ofBoolExprCached (mkFalseCollapsible 1) |>.aig.decls

/-- info: #[Decl.const false] -/
#guard_msgs in
#eval AIG.ofBoolExprCached (mkFalseCollapsible 16) |>.aig.decls
