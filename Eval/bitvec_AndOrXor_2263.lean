theorem bitvec_AndOrXor_2263 :
 ∀ (B op0 : BitVec 64), op0 ||| op0 ^^^ B = op0 ||| B
:= by alive_auto
      done --ext