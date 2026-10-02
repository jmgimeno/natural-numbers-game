import NaturalNumbersGame.MyNat
import NaturalNumbersGame.addition_world
import NaturalNumbersGame.multiplication_world
import NaturalNumbersGame.le_world

open MyNat

theorem mul_le_mul_right (a b t : MyNat) (h: a ≤ b) : a * t ≤ b * t := by
  cases h with
  | intro k hk =>
    rewrite [hk, add_mul]
    exists k * t

theorem mul_left_ne_zero (a b : MyNat) (h: a * b ≠ 0) : b ≠ 0 := by
  intro hb
  rewrite [hb] at h
  contradiction

theorem eq_succ_of_ne_zero (a : MyNat) (h: a ≠ 0) : ∃ n, a = succ n := by
  cases a with
  | zero =>
    contradiction
  | succ n =>
    exists n

theorem one_le_of_ne_zero (a : MyNat) (h: a ≠ 0) : 1 ≤ a := by
  cases eq_succ_of_ne_zero a h with
  | intro n hn =>
    rewrite [hn, succ_eq_add_one, add_comm]
    exists n

theorem le_mul_right (a b : MyNat) (h: a * b ≠ 0) : a ≤ a * b := by
  replace h := mul_left_ne_zero a b h
  replace h := one_le_of_ne_zero b h
  replace h := mul_le_mul_right 1 b a h
  rw [one_mul, mul_comm] at h
  exact h

theorem mul_right_eq_one (x y : MyNat) (h: x * y = 1) : x = 1 := by
  have h2 : x * y ≠ 0 := by
    intro h2
    rewrite [h2] at h
    contradiction
  have h4 : x ≤ 1 := by
    replace h4 := le_mul_right x y h2
    rewrite [h] at h4
    exact h4
  have h5 : 1 ≤ x := by
    apply one_le_of_ne_zero
    intro h5
    rewrite [h5] at h
    rw [zero_mul] at h
    contradiction
  exact le_antisymm x 1 h4 h5

theorem mul_ne_zero (a b : MyNat) (ha: a ≠ 0) (hb: b ≠ 0) : a * b ≠ 0 := by
  have h1 : 1 ≤ a := one_le_of_ne_zero a ha
  have h2 : 1 ≤ b := one_le_of_ne_zero b hb
  cases h1 with
  | intro k hk =>
    rw [add_comm, ← succ_eq_add_one] at hk
    cases h2 with
    | intro l hl =>
      rewrite [add_comm, ← succ_eq_add_one] at hl
      intro h3
      cases a with
      | zero =>
        contradiction
      | succ a' =>
        cases b with
        | zero =>
          contradiction
        | succ b' =>
          rewrite [mul_succ, add_succ] at h3
          symm at h3
          exact zero_ne_succ _ h3

theorem mul_eq_zero (a b : MyNat) (h: a * b = 0) : a = 0 ∨ b = 0 := by
  cases a with
  | zero =>
    left
    rfl
  | succ a' =>
    cases b with
    | zero =>
      right
      rfl
    | succ b' =>
      rewrite [mul_succ, add_succ] at h
      symm at h
      replace h := zero_ne_succ _ h
      contradiction

theorem mul_left_cancel (a b c : MyNat) (h: a * b = a * c) (ha: a ≠ 0) : b = c := by
  induction b generalizing c
  case zero =>
    rewrite [zero_eq_0, mul_zero] at h
    symm at h
    replace h := mul_eq_zero a c h
    cases h with
    | inl zero.a =>
      contradiction
    | inr zero.c =>
      symm
      rw [zero_eq_0]
      exact zero.c
  case succ b' ih =>
    cases c with
    | zero =>
      rewrite [zero_eq_0, mul_zero] at h
      replace h := mul_eq_zero a (succ b') h
      cases h with
      | inl zero.a =>
        contradiction
      | inr zero.b'.succ =>
        contradiction
    | succ c' =>
      repeat rewrite [mul_succ] at h
      replace h := add_right_cancel _ _ _ h
      rw [ih c' h]

theorem mul_right_eq_self (a b : MyNat) (h: a * b = a) (ha: a ≠ 0) : b = 1 := by
  rewrite (occs := .pos [2]) [← mul_one a] at h
  exact mul_left_cancel a b 1 h ha
