import NaturalNumbersGame.MyNat
import NaturalNumbersGame.tutorial_world
import NaturalNumbersGame.addition_world

open MyNat

example (h1: x + y = 37) (_: 3 * x + z = 42) : x + y = 37 := by
  exact h1

example {x y : MyNat} (h: 0 + x = (0 + y) + 2) : x = y + 2 := by
  repeat rw [zero_add] at h
  exact h

example {x y : MyNat} (h1: x = 37) (h2: x = 37 -> y = 42) : y = 42 := by
  apply h2
  exact h1

example {x : MyNat} (h1: x + 1 = 4) : x = 3 := by
  apply succ_inj
  rw [← succ_eq_add_one] at h1
  rw [four_eq_succ_three] at h1
  exact h1

example {x : MyNat} : x = 37 -> x = 37 := by
  intro h
  exact h

example {x : MyNat} : x + 1 = y + 1 -> x = y := by
  intro h
  apply succ_inj
  exact h

example { x y : MyNat } (h1: x = y) (h2: x ≠ y): False := by
  apply h2 -- x ≠ y is x = y → False
  exact h1

theorem zero_ne_one : (0 : MyNat) ≠ (1 : MyNat) := by
  rw [one_eq_succ_zero]
  apply zero_ne_succ

theorem one_ne_zero : (1 : MyNat) ≠ (0 : MyNat) := by
  symm
  apply zero_ne_one

theorem one_ne_two : (2 : MyNat) + (2 : MyNat) ≠ (5 : MyNat) := by
  rewrite [five_eq_succ_four]
  rewrite [four_eq_succ_three]
  rewrite [three_eq_succ_two]
  repeat rewrite [two_eq_succ_one]
  repeat rewrite [one_eq_succ_zero]
  repeat rewrite [add_succ]
  rewrite [zero_eq_0]
  rewrite [add_zero]
  intro h
  repeat replace h := succ_inj _ _ h -- we don't have apply at
  exact zero_ne_one h
