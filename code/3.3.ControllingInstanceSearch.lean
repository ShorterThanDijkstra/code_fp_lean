-- https://lean-lang.org/functional_programming_in_lean//Overloading-and-Type-Classes/Controlling-Instance-Search/#out-params
def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat
#eval (3 : Pos) + (5 : Nat)
#eval (3 : Nat) + (5 : Pos)
class HPlus (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ
instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat
#eval toString (HPlus.hPlus (3 : Pos) (5 : Nat))
#eval (HPlus.hPlus (3 : Pos) (5 : Nat) : Pos)
class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ
#eval HPlus.hPlus (3 : Pos) (5 : Nat)
instance [Add α] : HPlus α α α where
  hPlus := Add.add
#eval HPlus.hPlus (3 : Nat) (5 : Nat)
#check HPlus.hPlus (5 : Nat) (3 : Nat)
#check HPlus.hPlus (5 : Nat)
@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add
#check HPlus.hPlus (5 : Nat)
#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0