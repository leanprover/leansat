theorem bitvec_AndOrXor_709 :
 ∀ (a b d : BitVec 64), ofBool (a &&& b == b) &&& ofBool (a &&& d == d) = ofBool (a &&& (b ||| d) == b ||| d)
:= by alive_auto
      try sorry