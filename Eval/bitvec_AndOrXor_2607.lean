theorem bitvec_AndOrXor_2607 :
 ∀ (a b : BitVec 64), (a ||| b ^^^ -1) ^^^ (a ^^^ -1 ||| b) = a ^^^ b
:= by alive_auto
      done --ext