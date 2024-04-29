theorem bitvec_AndOrXor_2453 :
 ∀ (y x : BitVec 64), (x <ₛ y) ^^^ -1 = ofBool (x ≥ₛ y)
:= by alive_auto
      try sorry