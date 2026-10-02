-- Our definition of natural numbers

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
  deriving Repr

open MyNat

-- To make it easier to write numbers

def nat_to_mynat : Nat → MyNat
  | 0 => zero
  | n + 1 => succ (nat_to_mynat n)

instance : OfNat MyNat n where
  ofNat := nat_to_mynat n

-- Needed because the game does some magic
-- with induction allowing 0 and n + 1

theorem zero_eq_0 : zero = 0 := rfl

theorem one_eq_succ_zero : 1 = succ zero := rfl

theorem two_eq_succ_one : 2 = succ 1 := rfl

theorem three_eq_succ_two : 3 = succ 2 := rfl

theorem four_eq_succ_three : 4 = succ 3 := rfl

theorem five_eq_succ_four : 5 = succ 4 := rfl

-- Addition

def add (m : MyNat) (n : MyNat) : MyNat :=
  match n with
  | zero => m
  | succ n' => succ (add m n')

instance : Add MyNat where
  add := add

example : add 3 4 = 7 := by rfl

theorem add_zero (a : MyNat) : a + 0 = a := by
  rfl

theorem add_succ (a b : MyNat) : a + succ b = succ (a + b) := by
  rfl

theorem succ_inj (a b : MyNat) : succ a = succ b → a = b := by
  intro h
  injection h

theorem zero_ne_succ (a : MyNat) : 0 ≠ succ a := by
  intro h
  injection h

-- Multiplication

def mul (m : MyNat) (n : MyNat) : MyNat :=
  match n with
  | zero => zero
  | succ n' => add (mul m n') m

instance : Mul MyNat where
  mul := mul

example : mul 3 4 = 12 := by rfl

theorem mul_zero (a : MyNat) : a * 0 = 0 := by
  rfl

theorem mul_succ (a b : MyNat) : a * succ b = a * b + a:= by
  rfl

-- Exponentiation

def pow (m : MyNat) (n : MyNat) : MyNat :=
  match n with
  | zero => succ zero
  | succ n' => mul (pow m n') m

example : pow 2 4 = 16 := by rfl

@[default_instance]
instance : Pow MyNat MyNat where
  pow := pow

example : (2 : MyNat) ^ (4 : MyNat) = (16 : MyNat) := by rfl

theorem pow_zero (a : MyNat) : a ^ 0 = 1 := by
  rfl

theorem pow_succ (a b : MyNat) : a ^ succ b = a ^ b * a := by
  rfl

-- To decide equality of natural numbers

instance instDecidableEq : DecidableEq MyNat
| 0, 0 => isTrue <| by
  show 0 = 0
  rfl
| succ m, 0 => isFalse <| by
  show succ m ≠ 0
  symm
  exact zero_ne_succ m
| 0, succ n => isFalse <| by
  show 0 ≠ succ n
  exact zero_ne_succ n
| succ m, succ n =>
  match instDecidableEq m n with
  | isTrue (h : m = n) => isTrue <| by
    show succ m = succ n
    rw [h]
  | isFalse (h : m ≠ n) => isFalse <| by
    intro h2
    apply h
    injection h2
