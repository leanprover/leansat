theorem bitvec_AndOrXor_2264 :
 ∀ (A B : BitVec 64), A ||| A ^^^ -1 ^^^ B = A ||| B ^^^ -1
:= by alive_auto
      done --ext