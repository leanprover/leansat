
/-
This files contains theorems that we need to add additional operations. You can track what these
theorems are for and who is working on it in this sheet:
https://docs.google.com/spreadsheets/d/1AFUChxhNZhOC2XQEn_RXk3A1JwLeOP1OPbPjfYjdEUQ/edit?usp=sharing

Many of these theorems are based on:
- https://www21.in.tum.de/teaching/sar/SS20/7.pdf
- https://www.cs.cmu.edu/~15414/s22/lectures/16-bitblasting.pdf

Note: We are currently not necessarily looking for the most performant circuit to simulate an
operation but instead just for *some* circuit to bitblast to. Proving any of these theorems will
help in verifying that some bitblasted circuit corresponds to the behavior of a BitVec operation.

Note: We are not sore if this is the ideal formulation of these theorems given the `BitVec` theory
of Lean. They are merely written down from the versions above, there might very well be better
formulations etc.
-/

namespace BitVec

-- TODO: sshiftRight

-- LT.lt unsigned
theorem ult_eq_carry (x y : BitVec w) : BitVec.ult x y = !(carry w x (~~~y) true) := by
  sorry

-- LE.le unsigned
theorem ule_eq_carry (x y : BitVec w) : BitVec.ule x y = (carry w y (~~~x) true) := by
  sorry

-- NOTE: ult_eq_carry and ule_eq_carry are trivial corrolaries of each other, proving one trivially
-- closes the other -> just prove the one that's simpler.

-- NOTE: I'm not sure if this is the correct formulation of the theorem, the idea is
-- "do something different based on the sign bit"
-- LT.lt signed
theorem slt_eq_carry (x y : BitVec w) :
    BitVec.slt x y
      =
    if x.getLsb (w - 1) = y.getLsb (w - 1) then !(carry w x (~~~y) true) else (carry w x (~~~y) true) := by
 sorry

-- LE.le signed
theorem sle_eq_carry (x y : BitVec w) :
    BitVec.sle x y
      =
    if x.getLsb (w - 1) = y.getLsb (w - 1) then (carry w y (~~~x) true) else !(carry w y (~~~x) true) := by
 sorry

-- NOTE: slt_eq_carry and sle_eq_carry are trivial corrolaries of each other, proving one trivially
-- closes the other -> just prove the one that's simpler.

def mulAux (l r : BitVec w) (s : Nat) : BitVec w := sorry

theorem mulAux_zero (l r : BitVec w) : mulAux l r 0 = 0 := sorry
theorem mulAux_succ (l r : BitVec w) :
  mulAux l r (s + 1)
    =
  (mulAux l r s) + (if r.getLsb (s + 1) then (l <<< (s + 1)) else 0#w) := sorry

-- Mul.mul
theorem mul_eq_circuit (x y : BitVec w) (i : Nat) :
    (x * y).getLsb i
      =
    (mulAux l r (w - 1)).getLsb i := by
  sorry

-- TODO: is there even signed div/remainder??

-- TODO: Div.div unsigned
-- TODO: Div.div signed
-- TODO: Remainder signed
-- TODO: Remainder unsigned

-- signextend
theorem getLsb_signExtend (x : BitVec n) (m : Nat) :
    (x.signExtend m).getLsb i
      =
    ((i < m) && (if i < n then x.getLsb i else x.getLsb (n - 1))) := by
  sorry

-- rotateLeft
theorem getLsb_rotateLeft (x : BitVec w) (m : Nat) :
    (x.rotateLeft m).getLsb i
      =
    ((i < w) && (x.getLsb ((i + m) % w))) := by
  sorry

-- rotateRight
-- TODO: finish theorem
theorem getLsb_rotateRight (x : BitVec w) (m : Nat) :
    (x.rotateRight m).getLsb i
      =
    ((i < w) && (x.getLsb sorry)) := by
  sorry

end BitVec
