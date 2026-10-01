import NaturalNumbersGame.MyNat

open MyNat

theorem add_zero (a : MyNat) : a + 0 = a := by
  rfl

theorem add_succ (a b : MyNat) : a + succ b = succ (a + b) := by
  rfl
