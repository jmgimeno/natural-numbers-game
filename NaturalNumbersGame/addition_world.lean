import NaturalNumbersGame.MyNat
import NaturalNumbersGame.tutorial_world

open MyNat

theorem zero_add (n: MyNat) : zero + n = n := by
  induction n with
  | zero => rfl
  | succ n' ih => rw [add_succ, ih]

theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c' ih => rw [add_succ, ih, add_succ, add_succ]

theorem succ_add (a b : MyNat) : succ a + b = succ (a + b) := by
  induction b with
  | zero => rfl
  | succ b' ih => rw [add_succ, ih, add_succ]

theorem add_comm (a b : MyNat) : a + b = b + a := by
  induction b with
  | zero => rw [add_zero, zero_add]
  | succ b' ih => rw [succ_add, ← ih, add_succ]

theorem succ_eq_add_one (a : MyNat) : succ a = a + 1 := by
  rfl

theorem add_right_comm (a b c : MyNat) : a + b + c = a + c + b := by
  rw [add_assoc, add_assoc, add_comm b]
