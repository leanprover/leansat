theorem bitvec_AndOrXor_698 :
 ∀ (a b d : BitVec 64), ofBool (a &&& b == 0) &&& ofBool (a &&& d == 0) = ofBool (a &&& (b ||| d) == 0)
:= by alive_auto
      try sorry