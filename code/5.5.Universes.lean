-- https://lean-lang.org/functional_programming_in_lean//Functors___-Applicative-Functors___-and-Monads/Universes/#Functional-Programming-in-Lean--Functors___-Applicative-Functors___-and-Monads--Universes
#check Prop
#check Type
inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α
def myListOfNat : MyList Type :=
  .cons Nat .nil
inductive MyList (α : Type 1) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α
inductive MyList (α : Type u) : Type u where
  | nil : MyList α
  | cons : α → MyList α → MyList α
def myListOfNumbers : MyList Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList Type :=
  .cons Nat .nil
def myListOfList : MyList (Type → Type) :=
  .cons MyList .nil
def myListOfNumbers : MyList.{0} Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList.{1} Type :=
  .cons Nat .nil

def myListOfList : MyList.{1} (Type → Type) :=
  .cons MyList.{0} .nil
inductive Sum (α : Type u) (β : Type u) : Type u where
  | inl : α → Sum α β
  | inr : β → Sum α β
def stringOrNat : Sum String Nat := .inl "hello"

def typeOrType : Sum Type Type := .inr Nat
def stringOrType : Sum String Type := .inr Nat
inductive Sum (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
def stringOrType : Sum String Type := .inr Nat
def someTruePropositions : List Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]
def someTruePropositions : List.{0} Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]