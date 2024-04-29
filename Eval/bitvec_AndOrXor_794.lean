theorem bitvec_AndOrXor_794 :
 ∀ (a b : BitVec 64), (a >ₛ b) &&& ofBool (a != b) = (a >ₛ b)
:= by alive_auto
      try sorry