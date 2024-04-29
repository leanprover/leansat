theorem bitvec_AddSub_1624 :
 ∀ (A B : BitVec 64), (A ||| B) - (A ^^^ B) = A &&& B
:= by alive_auto
      try sorry