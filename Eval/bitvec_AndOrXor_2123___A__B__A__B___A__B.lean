theorem bitvec_AndOrXor_2123___A__B__A__B___A__B :
 ∀ (A B : BitVec 64), A &&& (B ^^^ -1) ||| A ^^^ B = A ^^^ B
:= by alive_auto
      done --ext