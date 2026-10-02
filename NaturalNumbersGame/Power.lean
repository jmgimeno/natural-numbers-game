import NaturalNumbersGame.MyNat
import NaturalNumbersGame.Numbers
import NaturalNumbersGame.multiplication_world

open MyNat

theorem pow_zero (a : MyNat) : a ^ 0 = 1 := by
  rfl

theorem pow_succ (a b : MyNat) : a ^ succ b = a ^ b * a := by
  rw [mul_comm]
  rfl
