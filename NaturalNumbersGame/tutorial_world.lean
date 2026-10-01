import NaturalNumbersGame.MyNat
import NaturalNumbersGame.Numbers
import NaturalNumbersGame.Addition

open MyNat

example (x q : MyNat): 37 * x + q = 37 * x + q := rfl

example (x y : MyNat) (h: y = x + 7): 2 * y = 2 * (x + 7) := by
  rewrite [h]
  rfl

example (x y : MyNat) (h: y = x + 7): 2 * y = 2 * (x + 7) := by
  rw [h]

example : 2 = succ (succ 0) := by
  rw [two_eq_succ_one, one_eq_succ_zero] -- or rfl

example (a b c : MyNat) : a + (b + 0) + (c + 0) = a + b + c := by
  repeat rewrite [add_zero] -- rfl can apply definition of + 0
  rfl

theorem succ_eq_add_one (n: MyNat) : succ n = n + 1 := by
  rewrite [one_eq_succ_zero] -- rfl can do it, but we want to show how to use rw
  rewrite [add_succ]
  rw [add_zero]

example : 2 + 2 = (4 : MyNat) := by
  rewrite [four_eq_succ_three, three_eq_succ_two]
  rw (occs := .pos [2]) [two_eq_succ_one] -- nth_rw 2 [two_eq_succ_one] is also possible
  rw [add_succ]
  rw [← succ_eq_add_one]
