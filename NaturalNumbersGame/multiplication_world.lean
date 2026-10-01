import NaturalNumbersGame.MyNat
import NaturalNumbersGame.Multiplication
import NaturalNumbersGame.Numbers

open MyNat

theorem mul_one (m : MyNat) : m * 1 = m := by
  rw [one_eq_succ_zero, mul_succ, zero_eq_0, mul_zero, zero_add]

theorem zero_mul (m : MyNat) : 0 * m = 0 := by
  induction m with
  | zero => rw [zero_eq_0, mul_zero]
  | succ m' ih => rw [mul_succ, ih, add_zero]

theorem succ_mul (a b : MyNat) : succ a * b = a * b + b := by
  induction b with
  | zero => rw [zero_eq_0, mul_zero, mul_zero, add_zero]
  | succ b' ih => rw [mul_succ, ih, mul_succ, add_assoc, add_succ, add_comm b' a, ← add_succ, add_assoc]

theorem mul_comm (a b : MyNat) : a * b = b * a := by
  induction b with
  | zero => rw [zero_eq_0, mul_zero, zero_mul]
  | succ b' ih => rw [mul_succ, ih, succ_mul]

theorem one_mul (m : MyNat) : 1 * m = m := by
  rw [mul_comm, mul_one]

theorem two_mul (m : MyNat) : 2 * m = m + m := by
  rw [two_eq_succ_one, succ_mul, one_mul]

theorem mul_add (a b c : MyNat) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => rw [zero_eq_0, add_zero, mul_zero, add_zero]
  | succ c' ih => rw [add_succ, mul_succ, ih, mul_succ, add_assoc]

theorem add_mul (a b c : MyNat) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c, mul_comm c]

theorem mul_assoc (a b c : MyNat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rewrite [zero_eq_0]; repeat rw [mul_zero]
  | succ c' ih => rw [mul_succ, ih, mul_succ, mul_add]
