import NaturalNumbersGame.MyNat
import NaturalNumbersGame.Numbers
import NaturalNumbersGame.addition_world

open MyNat

theorem add_right_cancel (a b n : MyNat) : a + n = b + n → a = b := by
  intro h
  induction n with
  | zero =>
    repeat rewrite [zero_eq_0] at h
    repeat rewrite [add_zero] at h
    exact h
  | succ n' ih =>
    repeat rewrite [add_succ] at h
    replace h := succ_inj _ _ h
    apply ih
    exact h

theorem add_left_cancel (a b n : MyNat) : n + a = n + b → a = b := by
  repeat rewrite [add_comm n]
  apply add_right_cancel

theorem add_left_eq_self (x y : MyNat) : x + y = y → x = 0 := by
  rewrite (occs := .pos [2]) [<- zero_add y]
  apply add_right_cancel

theorem add_right_eq_self (x y : MyNat) : x + y = x → y = 0 := by
  rewrite [add_comm]
  apply add_left_eq_self

theorem add_right_eq_zero (a b : MyNat) : a + b = 0 → a = 0 := by
  cases b with
  | zero =>
    rewrite [zero_eq_0, add_zero]
    intro h
    exact h
  | succ b' =>
    rewrite [add_succ]
    intro h
    symm at h
    replace h := zero_ne_succ _ h
    contradiction

theorem add_left_eq_zero (a b : MyNat) : a + b = 0 → b = 0 := by
  rewrite [add_comm]
  apply add_right_eq_zero
