import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AddSub_1152 :
 ∀ (y x : BitVec 1), x + y = x ^^^ y
:= by bv_decide
