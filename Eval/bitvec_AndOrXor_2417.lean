theorem bitvec_AndOrXor_2417 :
 ∀ (nx y : BitVec 64), (nx ^^^ -1 ||| y) ^^^ -1 = nx &&& (y ^^^ -1)
:= by alive_auto
      done --ext