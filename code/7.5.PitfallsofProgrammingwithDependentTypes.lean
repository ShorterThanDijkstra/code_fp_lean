-- https://lean-lang.org/functional_programming_in_lean//Programming-with-Dependent-Types/Pitfalls-of-Programming-with-Dependent-Types/#Functional-Programming-in-Lean--Programming-with-Dependent-Types--Pitfalls-of-Programming-with-Dependent-Types
def Nat.plusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => plusL n k + 1
def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1
def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => _
  | .cons x xs, ys => _
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => _
  | n + 1, k, .cons x xs, ys => _
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => .cons x (_ : Vect α (n.plusL k))
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => .cons x (appendL n k xs ys)
def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (appendL xs ys)
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => _
  | n + 1, k, .cons x xs, ys => _
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n + k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => _
  | k + 1 => _
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by⊢ 0 = Nat.plusR 0 0 rflAll goals completed! 🐙
  | k + 1 => _
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by⊢ 0 = Nat.plusR 0 0 rflAll goals completed! 🐙
  | k + 1 => (_ : k + 1 = Nat.plusR 0 k + 1)
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by⊢ 0 = Nat.plusR 0 0 rflAll goals completed! 🐙
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)
theorem plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by⊢ 0 = Nat.plusR 0 0 rflAll goals completed! 🐙
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys => _
theorem plusR_succ_left (n : Nat) :
    (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => byn:Nat⊢ (n + 1).plusR 0 = n.plusR 0 + 1 rflAll goals completed! 🐙
  | k + 1 => _
theorem plusR_succ_left (n : Nat) :
    (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => byn:Nat⊢ (n + 1).plusR 0 = n.plusR 0 + 1 rflAll goals completed! 🐙
  | k + 1 => congrArg (· + 1) (plusR_succ_left n k)
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys =>
    plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys =>
    plusR_succ_left n k ▸ .cons x (appendR n k xs ys)
def appendR : Vect α n → Vect α k → Vect α (n.plusR k)
  | .nil, ys => plusR_zero_left _ ▸ ys
  | .cons x xs, ys => plusR_succ_left _ _ ▸ .cons x (appendR xs ys)