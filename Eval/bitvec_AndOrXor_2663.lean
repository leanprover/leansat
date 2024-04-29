theorem bitvec_AndOrXor_2663 :
 ∀ (a b : BitVec 64), (a ≤ᵤ b) ^^^ ofBool (a != b) = (a ≥ᵤ b)
:= by alive_auto
      try sorry