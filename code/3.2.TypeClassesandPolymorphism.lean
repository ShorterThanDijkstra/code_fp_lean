-- https://lean-lang.org/functional_programming_in_lean//Overloading-and-Type-Classes/Type-Classes-and-Polymorphism/#tc-polymorphism
#check (IO.println)
#check @IO.println
def List.sumOfContents [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents
def List.sumOfContents [Add α] [Zero α] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents
def fourNats : List Nat := [1, 2, 3, 4]
#eval fourNats.sumOfContents
def fourPos : List Pos := [1, 2, 3, 4]
#eval fourPos.sumOfContents
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }