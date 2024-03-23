import LeanSAT.Reflect.Tactics.BVDecide

open BitVec

set_option trace.bv true in
theorem foo (h1 : 0#1 = 1#1) (h2 : (2 : BitVec 2) = 3) (h3 : x = 4#3)
    (h4 : x &&& y = y &&& x) : 4#5 = 5#5 := by
  bv_decide

set_option trace.bv true in
theorem all_features {x y : BitVec 256} (h : x = y) : (~~~x) &&& 1 = (~~~y) &&& 1#256 := by
  bv_decide
