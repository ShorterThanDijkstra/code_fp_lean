-- https://lean-lang.org/functional_programming_in_lean//Functors___-Applicative-Functors___-and-Monads/Structures-and-Inheritance/#Functional-Programming-in-Lean--Functors___-Applicative-Functors___-and-Monads--Structures-and-Inheritance
structure MythicalCreature where
  large : Bool
deriving Repr
#check MythicalCreature.mk
#check MythicalCreature.large
structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr
def troll : Monster where
  large := true
  vulnerability := "sunlight"
#check Monster.mk
#eval troll.toMythicalCreature
def troll : Monster := {large := true, vulnerability := "sunlight"}
def troll : Monster := ⟨true, "sunlight"⟩
def troll : Monster := ⟨⟨true⟩, "sunlight"⟩
#eval MythicalCreature.large troll
def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large
structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr
def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"
structure MonstrousAssistant extends Monster, Helper where
deriving Repr
def domesticatedTroll : MonstrousAssistant where
  large := true
  assistance := "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"
#check MonstrousAssistant.mk
#print MonstrousAssistant.toHelper
inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large
def nonsenseCreature : SizedCreature where
  large := false
  size := .large
abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)
def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by⊢ SizesMatch huldre
  decideAll goals completed! 🐙