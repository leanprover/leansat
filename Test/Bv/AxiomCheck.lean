import LeanSAT.Reflect.Tactics.BVDecide

open BitVec

set_option trace.bv true in
theorem bv_axiomCheck (x y : BitVec 1) : x + y = y + x := by
  bv_decide

/--
info: 'bv_axiomCheck' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Quot.sound,
 AIG.RelabelNat.State.Inv1.property,
 AIG.RelabelNat.State.Inv2.property]
-/
#guard_msgs in
#print axioms bv_axiomCheck
