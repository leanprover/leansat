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
theorem unit_5 {x y : BitVec 256} : x <<< y = x <<< y := by
  bv_decide

set_option trace.bv true in
theorem unit_6 {x y : BitVec 256} : x + y = y + x := by
  bv_decide

theorem bitvec_AndOrXor_135 :
 ∀ (X C1 C2 : BitVec 64), (X ^^^ C1) &&& C2 = X &&& C2 ^^^ C1 &&& C2
:= by bv_decide

theorem bitvec_AndOrXor_144 :
 ∀ (X C1 C2 : BitVec 64), (X ||| C1) &&& C2 = (X ||| C1 &&& C2) &&& C2
:= by bv_decide

theorem bitvec_AndOrXor_2063__X__C1__C2____X__C2__C1__C2 :
 ∀ (x C1 C : BitVec 64), x ^^^ C1 ||| C = (x ||| C) ^^^ C1 &&& ~~~C
:= by bv_decide

theorem bitvec_AndOrXor_2231__A__B__B__C__A___A__B__C :
 ∀ (A C B : BitVec 64), A ^^^ B ||| B ^^^ C ^^^ A = A ^^^ B ||| C
:= by bv_decide

theorem bitvec_AndOrXor_2243__B__C__A__B___B__A__C :
 ∀ (A C B : BitVec 64), (B ||| C) &&& A ||| B = B ||| A &&& C
:= by bv_decide

theorem bitvec_AndOrXor_2263 :
 ∀ (B op0 : BitVec 64), op0 ||| op0 ^^^ B = op0 ||| B
:= by bv_decide

theorem bitvec_AndOrXor_2264 :
 ∀ (A B : BitVec 64), A ||| A ^^^ -1 ^^^ B = A ||| B ^^^ -1
:= by bv_decide

theorem bitvec_AndOrXor_2265 :
 ∀ (A B : BitVec 64), A &&& B ||| A ^^^ B = A ||| B
:= by bv_decide

theorem bitvec_AndOrXor_2284 :
 ∀ (A B : BitVec 64), A ||| (A ||| B) ^^^ -1 = A ||| B ^^^ -1
:= by bv_decide

theorem bitvec_AndOrXor_2285 :
 ∀ (A B : BitVec 64), A ||| A ^^^ B ^^^ -1 = A ||| B ^^^ -1
:= by bv_decide

theorem bitvec_AndOrXor_2367 :
 ∀ (A C1 op1 : BitVec 64), A ||| C1 ||| op1 = A ||| op1 ||| C1
:= by bv_decide

theorem bitvec_AndOrXor_2595 :
 ∀ (a b : BitVec 64), a &&& b ^^^ (a ||| b) = a ^^^ b
:= by bv_decide

theorem bitvec_AndOrXor_2647 :
 ∀ (a b : BitVec 64), a &&& b ^^^ (a ^^^ b) = a ||| b
:= by bv_decide

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
