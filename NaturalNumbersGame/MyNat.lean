-- Our definition of natural numbers

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
  deriving Repr

open MyNat

def nat_to_mynat : Nat → MyNat
  | 0 => zero
  | n + 1 => succ (nat_to_mynat n)

instance : OfNat MyNat n where
  ofNat := nat_to_mynat n

def add (m : MyNat) (n : MyNat) : MyNat :=
  match n with
  | zero => m
  | succ n' => succ (add m n')

instance : Add MyNat where
  add := add

example : add 3 4 = 7 := by rfl

def mul (m : MyNat) (n : MyNat) : MyNat :=
  match n with
  | zero => zero
  | succ n' => add m (mul m n')

instance : Mul MyNat where
  mul := mul

example : mul 3 4 = 12 := by rfl
