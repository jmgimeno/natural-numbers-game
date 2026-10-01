import NaturalNumbersGame.MyNat

open MyNat

-- Needed because the game does some magic
-- with induction allowing 0 and n + 1
theorem zero_eq_0 : zero = 0 := rfl

theorem one_eq_succ_zero : 1 = succ zero := rfl

theorem two_eq_succ_one : 2 = succ 1 := rfl

theorem three_eq_succ_two : 3 = succ 2 := rfl

theorem four_eq_succ_three : 4 = succ 3 := rfl
