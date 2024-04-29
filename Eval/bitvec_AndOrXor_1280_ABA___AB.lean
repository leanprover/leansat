import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_1280_ABA___AB :
 ∀ (A B : BitVec 64), (A ^^^ -1 ||| B) &&& A = A &&& B
:= by bv_decide
