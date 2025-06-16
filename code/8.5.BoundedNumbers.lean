-- https://lean-lang.org/functional_programming_in_lean//Programming___-Proving___-and-Performance/Bounded-Numbers/#Functional-Programming-in-Lean--Programming___-Proving___-and-Performance--Bounded-Numbers
structure Fin (n : Nat) where
  val  : Nat
  isLt : LT.lt val n
def findHelper (arr : Array α) (p : α → Bool) (i : Nat) :
    Option (Fin arr.size × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (⟨i, h⟩, x)
    else findHelper arr p (i + 1)
  else none
def Array.find (arr : Array α) (p : α → Bool) : Option (Fin arr.size × α) :=
  findHelper arr p 0
#eval (3 : Fin 8).next?
#eval (7 : Fin 8).next?