theorem bitvec_AndOrXor_1704 :
 ∀ (A B : BitVec 64), ofBool (B == 0) ||| (A <ᵤ B) = (B + -1 ≥ᵤ A)
:= by alive_auto
      try sorry