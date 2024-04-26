import LeanSAT.Reflect.Tactics.BVDecide

/-
This file is based on: https://grack.com/blog/2022/12/20/deriving-a-bit-twiddling-hack/
-/

open BitVec

namespace DerivingBitTwiddlingHack

-- TODO: add version with ifs

/-
bool will_add_overflow_expression(int32_t a_, int32_t b_) {
    uint32_t a = (uint32_t)a_, b = (uint32_t)b_;
    uint32_t c = (uint32_t)a + (uint32_t)b;
    #define NEG(x) (((uint32_t)(x) & 0x80000000) == 0x80000000)
    return ((!NEG(a) && !NEG(b) && NEG(c))
        || (NEG(a) && NEG(b) && !NEG(c)));
    #undef NEG
}
-/

def will_add_overflow_expression (a b : BitVec 32) : Bool :=
  let c := a + b
  let NEG (x : BitVec 32) : Bool :=
    (x &&& 0x80000000#32) == 0x80000000#32
  (!NEG a && !NEG b && NEG c) || (NEG a && NEG b && !NEG c)

/-
bool will_add_overflow_bitwise(int32_t a_, int32_t b_) {
    uint32_t a = (uint32_t)a_, b = (uint32_t)b_;
    uint32_t c = (uint32_t)a + (uint32_t)b;
    #define NEG(x) (((uint32_t)(x) & 0x80000000) == 0x80000000)
    return ((!NEG(a) & !NEG(b) & NEG(c))
        | (NEG(a) & NEG(b) & !NEG(c)));
    #undef NEG
}
-/

def will_add_overflow_bitwise (a b : BitVec 32) : Bool :=
  let c := a + b
  let NEG (x : BitVec 32) : BitVec 1 :=
    ofBool ((x &&& 0x80000000#32) == 0x80000000#32)
  getLsb ((~~~NEG a &&& ~~~NEG b &&& NEG c) ||| (NEG a &&& NEG b &&& ~~~NEG c)) 0

example (a b : BitVec 32) : will_add_overflow_expression a b = will_add_overflow_bitwise a b := by
  dsimp [will_add_overflow_expression, will_add_overflow_bitwise]
  bv_decide

/-
bool will_add_overflow_bitwise_2(int32_t a_, int32_t b_) {
    uint32_t a = (uint32_t)a_, b = (uint32_t)b_;
    uint32_t c = (uint32_t)a + (uint32_t)b;
    #define NEG(x) (((uint32_t)(x) & 0x80000000) == 0x80000000)
    return NEG((~a & ~b & c) | (a & b & ~c));
    #undef NEG
}
-/
def will_add_overflow_bitwise_2 (a b : BitVec 32) : Bool :=
  let c := a + b
  let NEG (x : BitVec 32) : BitVec 1 :=
    ofBool ((x &&& 0x80000000#32) == 0x80000000#32)
  getLsb (NEG ((~~~a &&& ~~~b &&& c) ||| (a &&& b &&& ~~~c))) 0

example (a b : BitVec 32) : will_add_overflow_bitwise a b = will_add_overflow_bitwise_2 a b := by
  dsimp [will_add_overflow_bitwise, will_add_overflow_bitwise_2]
  bv_decide

/-
bool will_add_overflow_bitwise_3(int32_t a_, int32_t b_) {
    uint32_t a = (uint32_t)a_, b = (uint32_t)b_;
    uint32_t c = (uint32_t)a + (uint32_t)b;
    return ((~a & ~b & c) | (a & b & ~c)) >> 31;
}
-/
def will_add_overflow_bitwise_3 (a b : BitVec 32) : Bool :=
  let c := a + b
  getLsb (((~~~a &&& ~~~b &&& c) ||| (a &&& b &&& ~~~c)) >>> 31) 0

example (a b : BitVec 32) : will_add_overflow_bitwise_2 a b = will_add_overflow_bitwise_3 a b := by
  dsimp [will_add_overflow_bitwise_2, will_add_overflow_bitwise_3]
  bv_decide

/-
bool will_add_overflow_optimized_a(int32_t a_, int32_t b_) {
    uint32_t a = (uint32_t)a_, b = (uint32_t)b_;
    uint32_t c = (uint32_t)a + (uint32_t)b;
    return (~(a ^ b) & (c ^ a)) >> 31;
}
-/
def will_add_overflow_optimized_a (a b : BitVec 32) : Bool :=
  let c := a + b
  getLsb ((~~~(a ^^^ b) &&& (c ^^^ a)) >>> 31) 0

example (a b : BitVec 32) :
    will_add_overflow_bitwise_3 a b = will_add_overflow_optimized_a a b := by
  dsimp [will_add_overflow_bitwise_3, will_add_overflow_optimized_a]
  bv_decide

/-
bool will_add_overflow_optimized_b(int32_t a_, int32_t b_) {
    uint32_t a = (uint32_t)a_, b = (uint32_t)b_;
    uint32_t c = (uint32_t)a + (uint32_t)b;
    return ((c ^ a) & (c ^ b)) >> 31;
}
-/
def will_add_overflow_optimized_b (a b : BitVec 32) : Bool :=
  let c := a + b
  getLsb ((~~~(c ^^^ a) &&& (c ^^^ b)) >>> 31) 0

example (a b : BitVec 32) :
    will_add_overflow_optimized_a a b = will_add_overflow_optimized_b a b := by
  dsimp [will_add_overflow_optimized_a, will_add_overflow_optimized_b]
  bv_decide


end DerivingBitTwiddlingHack
