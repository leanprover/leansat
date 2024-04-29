theorem bitvec_AddSub_1614 :
 ∀ (Y X : BitVec 64), X - (X + Y) = 0 - Y
:= by alive_auto
      done --ring