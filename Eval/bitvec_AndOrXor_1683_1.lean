theorem bitvec_AndOrXor_1683_1 :
 ∀ (a b : BitVec 64), (a >ᵤ b) ||| ofBool (a == b) = (a ≥ᵤ b)
:= by alive_auto
      try sorry