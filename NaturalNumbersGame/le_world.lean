import NaturalNumbersGame.MyNat
import NaturalNumbersGame.addition_world
import NaturalNumbersGame.advanced_addition_world

open MyNat

theorem le_refl (x : MyNat) : x ≤ x := by
  exists 0

theorem zero_le (x : MyNat) : 0 ≤ x := by
  exists x
  rw [zero_add]

theorem le_succ_self (x : MyNat) : x ≤ succ x := by
  exists 1

theorem le_trans (x y z : MyNat) (hxy: x ≤ y) (hyz: y ≤ z) : x ≤ z := by
  cases hxy with
  | intro k hk => -- y = x + k
    cases hyz with
    | intro l hl => -- z = y + l
      rewrite [hl, hk, add_assoc]
      exists (k + l)

theorem le_zero (x : MyNat) (hx: x ≤ 0) : x = 0 := by
  cases hx with
  | intro k hk =>
    symm at hk
    replace hk := add_right_eq_zero _ _ hk
    exact hk

theorem le_antisymm (x y : MyNat) (hxy: x ≤ y) (hyx: y ≤ x) : x = y := by
  cases hxy with
  | intro k hk =>
    cases hyx with
    | intro l hl =>
      rewrite [hk]
      rewrite [hk, add_assoc] at hl
      symm at hl
      replace hl := add_right_eq_self _ _ hl
      replace hl := add_right_eq_zero _ _ hl
      rw [hl, add_zero]

example (x y : MyNat) (h: x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  cases h with
  | inl hx =>
    right
    exact hx
  | inr hy =>
    left
    exact hy

theorem le_total (x y : MyNat) : x ≤ y ∨ y ≤ x := by
  induction y with
  | zero =>
    right
    exact zero_le x
  | succ y' ih =>
    cases ih with
    | inl hxy =>
      left
      cases hxy with
      | intro k hk =>
        exists (succ k)
        rw [hk, add_succ]
    | inr hyx =>
      cases hyx with
      | intro l hl =>
        cases l with
        | zero =>
          rewrite [zero_eq_0, add_zero] at hl
          left
          rewrite [hl]
          exists 1
        | succ l' =>
          rewrite [add_succ, add_comm, ← add_succ, add_comm] at hl
          right
          exists l'

theorem succ_le_succ (x y : MyNat) (h: succ x ≤ succ y) : x ≤ y := by
  cases h with
  | intro k hk =>
    rewrite [succ_add] at hk
    replace hk := succ_inj _ _ hk
    exists k

theorem le_one (x : MyNat) (h: x ≤ 1) : x = 0 ∨ x = 1 := by
  cases h with
  | intro k hk =>
    cases k with
    | zero =>
      right
      rewrite [zero_eq_0, add_zero] at hk
      symm at hk
      exact hk
    | succ k' =>
      left
      rewrite [add_succ] at hk
      rewrite [one_eq_succ_zero] at hk
      replace hk := succ_inj _ _ hk
      rewrite [zero_eq_0] at hk
      symm at hk
      exact add_right_eq_zero _ _ hk

theorem le_two (x : MyNat) (h: x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  cases h with
  | intro k hk =>
    cases k with
    | zero =>
      rewrite [zero_eq_0, add_zero] at hk
      symm at hk
      right
      right
      exact hk
    | succ k' =>
      rw [add_succ] at hk
      rw [two_eq_succ_one] at hk
      replace hk := succ_inj _ _ hk
      cases k' with
      | zero =>
        rw [zero_eq_0, add_zero] at hk
        symm at hk
        right
        left
        exact hk
      | succ k'' =>
        rw [add_succ, one_eq_succ_zero, zero_eq_0] at hk
        replace hk := succ_inj _ _ hk
        symm at hk
        replace hk := add_right_eq_zero _ _ hk
        left
        exact hk
