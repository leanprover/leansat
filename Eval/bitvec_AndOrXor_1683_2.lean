theorem bitvec_AndOrXor_1683_2 :
 ∀ (a b : BitVec 64), (a ≥ᵤ b) ||| ofBool (a != b) = ofBool true
:= by alive_auto
      try sorry