-- https://lean-lang.org/functional_programming_in_lean//Getting-to-Know-Lean/Functions-and-Definitions/#Functional-Programming-in-Lean--Getting-to-Know-Lean--Functions-and-Definitions
def hello := "Hello"
def lean : String := "Lean"
#eval String.append hello (String.append " " lean)
def add1 (n : Nat) : Nat := n + 1
#eval add1 7
def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n
def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)
maximum (5 + 8) (2 * 7)
maximum 13 14
if 13 < 14 then 14 else 13
14
def Str : Type := String
def aStr : Str := "This is a string."
def NaturalNumber : Type := Nat
def thirtyEight : NaturalNumber := 38
def thirtyEight : NaturalNumber := (38 : Nat)
abbrev N : Type := Nat
def thirtyNine : N := 39