import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AddSub_1624 :
 ∀ (A B : BitVec 64), (A ||| B) - (A ^^^ B) = A &&& B
:= by bv_decide
