import LeanSAT.BitBlast.BoolExpr

open Std.Sat

def mkFalseCollapsible (n : Nat) : BoolExpr Nat :=
  match n with
  | 0 => .const false
  | n + 1 =>
    let tree := mkFalseCollapsible n
    .gate .and tree tree

/-- info: #[Std.Sat.AIG.Decl.const false] -/
#guard_msgs in
#eval AIG.ofBoolExprCachedDirect (mkFalseCollapsible 1) |>.aig.decls

/-- info: #[Std.Sat.AIG.Decl.const false] -/
#guard_msgs in
#eval AIG.ofBoolExprCachedDirect (mkFalseCollapsible 16) |>.aig.decls

def mkTrueCollapsible (n : Nat) : BoolExpr Nat :=
  match n with
  | 0 => .const true
  | n + 1 =>
    let tree := mkTrueCollapsible n
    .gate .and tree tree

/-- info: #[Std.Sat.AIG.Decl.const true] -/
#guard_msgs in
#eval AIG.ofBoolExprCachedDirect (mkTrueCollapsible 1) |>.aig.decls

/-- info: #[Std.Sat.AIG.Decl.const true] -/
#guard_msgs in
#eval AIG.ofBoolExprCachedDirect (mkTrueCollapsible 16) |>.aig.decls

def mkConstantCollapsible (n : Nat) : BoolExpr Nat :=
  match n with
  | 0 => .const false
  | n + 1 =>
    let tree := mkTrueCollapsible n
    .gate .and (.gate .and tree tree) (.const false)

/-- info: (2, Std.Sat.AIG.Decl.const false) -/
#guard_msgs in
#eval
  let entry := AIG.ofBoolExprCachedDirect (mkConstantCollapsible 1)
  (entry.aig.decls.size, entry.aig.decls[entry.ref.gate]!)

/-- info: (2, Std.Sat.AIG.Decl.const false) -/
#guard_msgs in
#eval
  let entry := AIG.ofBoolExprCachedDirect (mkConstantCollapsible 16)
  (entry.aig.decls.size, entry.aig.decls[entry.ref.gate]!)
