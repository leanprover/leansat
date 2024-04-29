import LeanSAT.Reflect.Tactics.BVDecide

theorem bitvec_AndOrXor_1288_A__B__B__C__A___A__B__C :
 ∀ (A C B : BitVec 64), (A ^^^ B) &&& (B ^^^ C ^^^ A) = (A ^^^ B) &&& (C ^^^ -1)
:= by bv_decide
