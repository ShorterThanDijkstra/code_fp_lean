-- https://lean-lang.org/functional_programming_in_lean//Programming-with-Dependent-Types/Indexed-Families/#Functional-Programming-in-Lean--Programming-with-Dependent-Types--Indexed-Families
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
example : Vect String 3 :=
  .cons "one" (.cons "two" (.cons "three" .nil))
example : Vect String 3 := Vect.nil
example : Vect String n := Vect.nil
example : Vect String n := Vect.cons "Hello" (Vect.cons "world" Vect.nil)
def Vect.replicate (n : Nat) (x : α) : Vect α n := _
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => _
  | k + 1 => _
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons _ _
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)
def List.replicate (n : Nat) (x : α) : List α :=
  match n with
  | 0 => []
  | k + 1 => x :: x :: replicate k x
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (.cons x (replicate k x))
["Mount Hood",
 "Mount Jefferson",
 "South Sister"].zip ["Møllehøj", "Yding Skovhøj", "Ejer Bavnehøj"]
[("Mount Hood", "Møllehøj"),
 ("Mount Jefferson", "Yding Skovhøj"),
 ("South Sister", "Ejer Bavnehøj")]
[3428.8, 3201, 3158.5, 3075, 3064].zip [170.86, 170.77, 170.35]
[(3428.8, 170.86), (3201, 170.77), (3158.5, 170.35)]
def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)
def List.zip : List α → List β → List (α × β)
  | [], [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys
def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .nil, .cons y ys => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)
def Vect.zip : (n : Nat) → Vect α n → Vect β n → Vect (α × β) n
  | 0, .nil, .nil => .nil
  | k + 1, .cons x xs, .cons y ys => .cons (x, y) (zip k xs ys)