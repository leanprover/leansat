import LeanSAT.Tactics.BVDecide

open Std (BitVec)
theorem mul_of_pow2s_thm (x x_1 : _root_.BitVec 32) :
    (x_1 &&& 8#32) * (x &&& 16#32) ||| 128#32 = 128#32 := by
  bv_decide

