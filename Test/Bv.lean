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

set_option trace.bv true in
theorem unit_4 {x y : BitVec 256} : x <<< 257 = y <<< 258 := by
  bv_decide

-- This demonstrates we correctly abstract shifts of arbitrary width as atoms instead of giving up.
set_option trace.bv true in
theorem unit_5 {x y : BitVec 256} : (x <<< y) + y = y + (x <<< y) := by
  bv_decide

set_option trace.bv true in
theorem unit_6 {x y : BitVec 256} : x + y = y + x := by
  bv_decide

set_option trace.bv true in
theorem unit_7 {x y : BitVec 256} : x >>> 257 = y >>> 258 := by
  bv_decide

-- This demonstrates we correctly abstract shifts of arbitrary width as atoms instead of giving up.
set_option trace.bv true in
theorem unit_8 {x y : BitVec 256} : (x >>> y) + y = y + (x >>> y) := by
  bv_decide

set_option trace.bv true in
theorem unit_9 {x : BitVec 32} : (x.zeroExtend 64).zeroExtend 128 = x.zeroExtend 128 := by
  bv_decide

set_option trace.bv true in
theorem unit_10 {x : BitVec 256} : (x.zeroExtend 512).zeroExtend 128 = x.zeroExtend 128 := by
  bv_decide

theorem unit_11 {x : BitVec 256} : x = x := by
  bv_decide

theorem unit_12 {x : BitVec 256} (h : ¬(x = x)) : x = 0 := by
  bv_decide

set_option trace.bv true in
theorem unit_13 {x y : BitVec 256} : (x = y) ∨ (x ≠ y) := by
  bv_decide

set_option trace.bv true in
theorem unit_13' {x y : BitVec 256} : (x = y) || (x ≠ y) := by
  bv_decide

set_option trace.bv true in
theorem unit_14 {x y : BitVec 256} : (x = y) → (x + y = y + x) := by
  bv_decide

theorem unit_15 {x y : BitVec 256} : x = x ∧ y = y := by
  bv_decide

set_option trace.bv true in
theorem unit_16 {x y z : BitVec 256} : (x = y ∧ x = z) → (x = z) := by
  bv_decide

set_option trace.bv true in
theorem unit_17 {x y : BitVec 256} : xor (x = y) (x ≠ y) := by
  bv_decide

set_option trace.bv true in
theorem unit_18 {x y : BitVec 256} : (x = y) ↔ (y = x) := by
  bv_decide

theorem unit_19 {x : BitVec 256} : -x = (~~~x) + 1 := by
  bv_decide

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
