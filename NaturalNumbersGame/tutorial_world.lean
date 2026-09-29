import NaturalNumbersGame.MyNat

open MyNat

theorem example1 (x y z : MyNat) : x * y + z = x * y + z := by
  rfl

theorem example2 (x y : MyNat) (h: y = x + 7) : 2 * y = 2 * (x + 7) := by
  rewrite [h]
  rfl

theorem example3 (a b : MyNat) (h: succ a = b) : succ (succ a) = succ b := by
  rw [h]

theorem add_zero (a : MyNat) : a + zero = a := by
  rfl

theorem add_succ (a b : MyNat) : a + succ b = succ (a + b) := by
  rfl
