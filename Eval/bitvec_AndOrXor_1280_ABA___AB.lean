theorem bitvec_AndOrXor_1280_ABA___AB :
 ∀ (A B : BitVec 64), (A ^^^ -1 ||| B) &&& A = A &&& B
:= by alive_auto
      done --ext