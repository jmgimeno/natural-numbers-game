import NaturalNumbersGame.MyNat
import NaturalNumbersGame.addition_world

open MyNat

theorem add_left_comm (a b c : MyNat) : a + (b + c) = b + (a + c) := by
  rw [add_comm, add_assoc, add_comm c]

example (a b c d : MyNat) : (a + b) + (c + d) = ((a + c) + d) + b := by
  rewrite [add_assoc, add_comm b]
  repeat rw [← add_assoc]

example (a b c d e f g h : MyNat)
  : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_left_comm, add_comm]

macro "simp_add" : tactic => `(tactic|(
  simp only [add_assoc, add_left_comm, add_comm]))

example (a b c d e f g h : MyNat)
  : d + f + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp_add

def pred (m : MyNat) : MyNat :=
  match m with
  | zero => zero
  | succ m' => m'

theorem pred_succ (m : MyNat) : pred (succ m) = m := by rfl

def is_zero (m : MyNat) : Prop :=
  match m with
  | zero => True
  | succ _ => False

theorem is_zero_zero : is_zero 0 := by
  rw [← zero_eq_0]
  simp [is_zero]

theorem is_zero_succ (m : MyNat) : is_zero (succ m) = False := by
  simp [is_zero]

example (a b : MyNat) (h : succ a = succ b) : a = b := by
  rw [← pred_succ a, ← pred_succ b, h]

theorem succ_ne_zero (a : MyNat) : succ a ≠ 0 := by
  intro h
  symm at h
  apply zero_ne_succ a
  exact h

theorem succ_ne_succ (a b : MyNat) : a ≠ b → succ a ≠ succ b := by
  intro h1 h2
  apply h1
  injection h2

example : (20 : MyNat) + (20 : MyNat) = (40 : MyNat) := by
  decide -- rfl works too

example : (2 : MyNat) + (2 : MyNat) ≠  (5 : MyNat) := by
  decide -- rfl works
