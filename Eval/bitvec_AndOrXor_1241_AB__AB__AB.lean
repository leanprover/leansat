import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_1241_AB__AB__AB :
 ∀ (A B : BitVec 64), (A ||| B) &&& (A &&& B ^^^ -1) = A ^^^ B
:= by bv_decide
