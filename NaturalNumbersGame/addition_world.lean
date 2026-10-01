import NaturalNumbersGame.MyNat
import NaturalNumbersGame.tutorial_world

open MyNat

theorem zero_add (n: MyNat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n' ih => rw [add_succ, ih]

theorem succ_add (a b : MyNat) : succ a + b = succ (a + b) := by
  induction b with
  | zero => rfl
  | succ b' ih => rw [add_succ, ih, add_succ]

theorem add_comm (a b : MyNat) : a + b = b + a := by
  induction b with
  | zero => rw [zero_eq_0, zero_add, add_zero]
  | succ b' ih => rw [succ_add, ← ih, add_succ]

theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c' ih => rw [add_succ, ih, add_succ, add_succ]


theorem add_right_comm (a b c : MyNat) : (a + b) + c = (a + c) + b := by
  rw [add_assoc, add_assoc, add_comm b]
