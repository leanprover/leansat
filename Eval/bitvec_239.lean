theorem bitvec_239 :
 ∀ (Y X : BitVec 64), (0 - X) * (0 - Y) = X * Y
:= by alive_auto
      done --ring