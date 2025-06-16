-- https://lean-lang.org/functional_programming_in_lean//Overloading-and-Type-Classes/Positive-Numbers/#positive-numbers
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
def seven : Pos := 7
def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))
def fourteen : Pos := seven + seven
def fortyNine : Pos := seven * seven
#eval Plus.plus 5 3
class Plus (α : Type) where
  plus : α → α → α
instance : Plus Nat where
  plus := Nat.add
open Plus (plus)
#eval plus 5 3
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def fourteen : Pos := plus seven seven
#eval plus 5.2 917.25861
instance : Add Pos where
  add := Pos.plus
def fourteen : Pos := seven + seven
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
instance : ToString Pos where
  toString := posToString true
#eval s!"There are {seven}"
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
instance : ToString Pos where
  toString x := toString (x.toNat)
#eval s!"There are {seven}"
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul
#eval [seven * Pos.one,
       seven * seven,
       Pos.succ Pos.one * seven]
class Zero (α : Type) where
  zero : α
class OfNat (α : Type) (_ : Nat) where
  ofNat : α
inductive LT4 where
  | zero
  | one
  | two
  | three
deriving Repr
instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three
#eval (3 : LT4)
#eval (0 : LT4)
#eval (4 : LT4)
instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n
def eight : Pos := 8
def zero : Pos := 0
structure Pos where
  succ ::
  pred : Nat