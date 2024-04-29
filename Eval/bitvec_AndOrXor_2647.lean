theorem bitvec_AndOrXor_2647 :
 ∀ (a b : BitVec 64), a &&& b ^^^ (a ^^^ b) = a ||| b
:= by alive_auto
      done --ext