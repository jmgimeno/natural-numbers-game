import NaturalNumbersGame.MyNat
import NaturalNumbersGame.addition_world

open MyNat

theorem mul_zero (a : MyNat) : a * 0 = 0 := by
  rfl

theorem mul_succ (a b : MyNat) : a * succ b = a * b + a:= by
  rw [add_comm]
  rfl
