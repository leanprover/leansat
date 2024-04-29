theorem bitvec_AndOrXor_827 :
 ∀ (a b : BitVec 64), ofBool (a == 0) &&& ofBool (b == 0) = ofBool (a ||| b == 0)
:= by alive_auto
      try sorry