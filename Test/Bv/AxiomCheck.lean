import LeanSAT.Reflect.Tactics.BVDecide

open BitVec

set_option trace.bv true in
theorem bv_axiomCheck (x y : BitVec 1) : x + y = y + x := by
  bv_decide

/--
info: 'bv_axiomCheck' depends on axioms: [Classical.choice,
 propext,
 Quot.sound,
 AIG.RelabelNat.State.Inv1.property,
 AIG.RelabelNat.State.Inv2.property,
 Lean.ofReduceBool]
-/
#guard_msgs in
#print axioms bv_axiomCheck
