theorem bitvec_AndOrXor_2118___A__B__A___A__B :
 ∀ (A B : BitVec 64), A &&& B ||| A ^^^ -1 = A ^^^ -1 ||| B
:= by alive_auto
      done --ext