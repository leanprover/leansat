theorem bitvec_AndOrXor_1253_A__AB___A__B :
 ∀ (A B : BitVec 64), (A ^^^ B) &&& A = A &&& (B ^^^ -1)
:= by alive_auto
      done --ext