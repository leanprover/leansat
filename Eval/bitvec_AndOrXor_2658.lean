theorem bitvec_AndOrXor_2658 :
 ∀ (a b : BitVec 64), a &&& (b ^^^ -1) ^^^ (a ^^^ -1) = a &&& b ^^^ -1
:= by alive_auto
      done --ext