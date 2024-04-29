theorem bitvec_AndOrXor_1733 :
 ∀ (A B : BitVec 64), ofBool (A != 0) ||| ofBool (B != 0) = ofBool (A ||| B != 0)
:= by alive_auto
      try sorry