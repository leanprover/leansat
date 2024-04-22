import LeanSAT.Reflect.Tactics.BVDecide

open BitVec

set_option trace.bv true in
theorem unit_1 (h1 : 0#1 = 1#1) (h2 : (2 : BitVec 2) = 3) (h3 : x = 4#3)
    (h4 : x &&& y = y &&& x) : 4#5 = 5#5 := by
  bv_decide

set_option trace.bv true in
theorem unit_2 {x y : BitVec 256} (h : x = y) : (~~~x) &&& 1 = (~~~y) &&& 1#256 := by
  bv_decide

set_option trace.bv true in
theorem unit_3 {x y : BitVec 256} : ~~~(x &&& y) = (~~~x ||| ~~~y) := by
  bv_decide

theorem bv_axiomCheck (x : BitVec 1) : x = x := by bv_decide

/--
info: 'bv_axiomCheck' depends on axioms: [propext,
 Quot.sound,
 Classical.choice,
 AIG.RelabelNat.State.Inv1.property,
 AIG.RelabelNat.State.Inv2.property,
 Lean.ofReduceBool]
-/
#guard_msgs in
#print axioms bv_axiomCheck
