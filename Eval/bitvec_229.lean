theorem bitvec_229 :
 ∀ (X C1 Op1 : BitVec 64), (X + C1) * Op1 = X * Op1 + C1 * Op1
:= by alive_auto
      done --ring