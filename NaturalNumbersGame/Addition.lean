import NaturalNumbersGame.MyNat

open MyNat

theorem add_zero (a : MyNat) : a + 0 = a := by
  rfl

theorem add_succ (a b : MyNat) : a + succ b = succ (a + b) := by
  rfl

theorem succ_inj (a b : MyNat) : succ a = succ b → a = b := by
  intro h
  injection h with h1

theorem zero_ne_succ (a : MyNat) : 0 ≠ succ a := by
  intro h
  injection h
