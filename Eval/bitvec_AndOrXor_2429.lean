theorem bitvec_AndOrXor_2429 :
 ∀ (y x : BitVec 64), x &&& y ^^^ -1 = x ^^^ -1 ||| y ^^^ -1
:= by alive_auto
      done --ext