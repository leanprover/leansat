theorem bitvec_AddSub_1619 :
 ∀ (Y X : BitVec 64), X - Y - X = 0 - Y
:= by alive_auto
      done --ring