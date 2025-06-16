-- https://lean-lang.org/functional_programming_in_lean//Programming___-Proving___-and-Performance/Tail-Recursion/#tail-recursion
def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs
NonTail.sum [1, 2, 3]
1 + (NonTail.sum [2, 3])
1 + (2 + (NonTail.sum [3]))
1 + (2 + (3 + (NonTail.sum [])))
1 + (2 + (3 + 0))
1 + (2 + 3)
1 + 5
6
1 + (NonTail.sum [2, 3])
1 + (2 + (NonTail.sum [3]))
def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs
Tail.sum [1, 2, 3]
Tail.sumHelper 0 [1, 2, 3]
Tail.sumHelper (0 + 1) [2, 3]
Tail.sumHelper 1 [2, 3]
Tail.sumHelper (1 + 2) [3]
Tail.sumHelper 3 [3]
Tail.sumHelper (3 + 3) []
Tail.sumHelper 6 []
6
def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]
NonTail.reverse [1, 2, 3]
(NonTail.reverse [2, 3]) ++ [1]
((NonTail.reverse [3]) ++ [2]) ++ [1]
(((NonTail.reverse []) ++ [3]) ++ [2]) ++ [1]
(([] ++ [3]) ++ [2]) ++ [1]
([3] ++ [2]) ++ [1]
[3, 2] ++ [1]
[3, 2, 1]
def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs
Tail.reverse [1, 2, 3]
Tail.reverseHelper [] [1, 2, 3]
Tail.reverseHelper [1] [2, 3]
Tail.reverseHelper [2, 1] [3]
Tail.reverseHelper [3, 2, 1] []
[3, 2, 1]
def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)
def NonTail.length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1
def NonTail.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)
def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs