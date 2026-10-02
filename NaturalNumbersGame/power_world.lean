import NaturalNumbersGame.MyNat
import NaturalNumbersGame.Numbers
import NaturalNumbersGame.Power
import NaturalNumbersGame.multiplication_world

open MyNat

theorem zero_pow_zero : 0 ^ 0 = 1 := by
  rfl

theorem zero_pow_succ (n : MyNat) : 0 ^ succ n = 0 := by
  rw [pow_succ, mul_zero]

theorem pow_one (a : MyNat) : a ^ 1 = a := by
  rw [one_eq_succ_zero, pow_succ, zero_eq_0, pow_zero, one_mul]

theorem one_pow (n : MyNat) : 1 ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih, one_mul]

theorem pow_two (a : MyNat) : a ^ 2 = a * a := by
  rw [two_eq_succ_one, pow_succ, pow_one]

theorem pow_add (a m n : MyNat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
    repeat rewrite [zero_eq_0]
    rw [add_zero, pow_zero, mul_one]
  | succ n' ih =>
    rewrite [add_succ]
    repeat rewrite [pow_succ]
    rw [ih, mul_assoc]

theorem mul_pow (a b n : MyNat) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero =>
    repeat rewrite [zero_eq_0]
    repeat rewrite [pow_zero]
    rw [one_mul]
  | succ n' ih =>
    repeat rewrite [pow_succ]
    rewrite [ih, mul_assoc]
    rewrite (occs := pos [2]) [← mul_assoc]
    rw [mul_comm (b ^ n') a, mul_assoc, ← mul_assoc]

theorem pow_pow (a m n : MyNat) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero =>
    repeat rewrite [zero_eq_0]
    rewrite [mul_zero]
    repeat rw [pow_zero]
  | succ n' ih =>
    rw [pow_succ, ih, mul_succ, pow_add]

theorem add_sq (a b : MyNat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  repeat rewrite [pow_two]
  rewrite [mul_add]
  repeat rewrite [add_mul]
  rewrite [mul_assoc 2 _ _]
  rewrite [two_mul]
  rewrite [mul_comm b a]
  rewrite [← add_assoc _ _ (b * b)]
  rw [add_assoc (a * a) _ _]
