import LeanSAT.Frontend.BVDecide

open BitVec

theorem bitvec_AndOrXor_2443 :
 ∀ (y x : BitVec 64),  sshiftRight (x ^^^ -1) (BitVec.toNat y) ^^^ -1 = sshiftRight x (BitVec.toNat y)
:= by intros; bv_decide
