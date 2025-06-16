-- https://lean-lang.org/functional_programming_in_lean//Getting-to-Know-Lean/Datatypes-and-Patterns/#datatypes-and-patterns
inductive Bool where
  | false : Bool
  | true : Bool
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false
isZero Nat.zero
match Nat.zero with
| Nat.zero => true
| Nat.succ k => false
true
isZero 5
isZero (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
match Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) with
| Nat.zero => true
| Nat.succ k => false
false
#eval pred 5
#eval pred 839
#eval pred 0
def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k
pred 5
pred (Nat.succ 4)
match Nat.succ 4 with
| Nat.zero => Nat.zero
| Nat.succ k => k
4
def depth (p : Point3D) : Float :=
  match p with
  | { x:= h, y := w, z := d } => d
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)
def evenLoops (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (evenLoops n)
def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')
plus 3 2
plus 3 (Nat.succ (Nat.succ Nat.zero))
match Nat.succ (Nat.succ Nat.zero) with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k')
Nat.succ (plus 3 (Nat.succ Nat.zero))
Nat.succ (match Nat.succ Nat.zero with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k'))
Nat.succ (Nat.succ (plus 3 Nat.zero))
Nat.succ (Nat.succ (match Nat.zero with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k')))
Nat.succ (Nat.succ 3)
5
def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')
def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')
def div (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else Nat.succ (div (n - k) k)