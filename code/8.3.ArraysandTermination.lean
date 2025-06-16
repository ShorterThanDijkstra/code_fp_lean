-- https://lean-lang.org/functional_programming_in_lean//Programming___-Proving___-and-Performance/Arrays-and-Termination/#Functional-Programming-in-Lean--Programming___-Proving___-and-Performance--Arrays-and-Termination
class LE (α : Type u) where
  le : α → α → Prop

class LT (α : Type u) where
  lt : α → α → Prop
instance : LE Nat where
  le := Nat.le
inductive EasyToProve : Prop where
  | heresTheProof : EasyToProve
theorem fairlyEasy : EasyToProve := by⊢ EasyToProve
  constructorAll goals completed! 🐙
inductive True : Prop where
  | intro : True
inductive IsThree : Nat → Prop where
  | isThree : IsThree 3
theorem three_is_three : IsThree 3 := by⊢ IsThree 3
  constructorAll goals completed! 🐙
inductive IsFive : Nat → Prop where
  | isFive : IsFive 5
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := byn:Nat⊢ IsThree n → IsFive (n + 2)
  skipn:Nat⊢ IsThree n → IsFive (n + 2)
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := byn:Nat⊢ IsThree n → IsFive (n + 2)
  intro threen:Natthree:IsThree n⊢ IsFive (n + 2)
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := byn:Nat⊢ IsThree n → IsFive (n + 2)
  intro threen:Natthree:IsThree n⊢ IsFive (n + 2)
  constructorn:Natthree:IsThree n⊢ IsFive (n + 2)
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := byn:Nat⊢ IsThree n → IsFive (n + 2)
  intro threen:Natthree:IsThree n⊢ IsFive (n + 2)
  cases three with
  | isThree => skipisThree⊢ IsFive (3 + 2)
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := byn:Nat⊢ IsThree n → IsFive (n + 2)
  intro threen:Natthree:IsThree n⊢ IsFive (n + 2)
  cases three with
  | isThree => constructorAll goals completed! 🐙
theorem four_is_not_three : ¬ IsThree 4 := by⊢ ¬IsThree 4
  skip⊢ ¬IsThree 4
theorem four_is_not_three : ¬ IsThree 4 := by⊢ ¬IsThree 4
  unfold Not⊢ IsThree 4 → False
theorem four_is_not_three : ¬ IsThree 4 := by⊢ ¬IsThree 4
  intro hh:IsThree 4⊢ False
theorem four_is_not_three : ¬ IsThree 4 := by⊢ ¬IsThree 4
  intro hh:IsThree 4⊢ False
  cases hAll goals completed! 🐙
inductive Nat.le (n : Nat) : Nat → Prop
  | refl : Nat.le n n
  | step : Nat.le n m → Nat.le n (m + 1)
theorem four_le_seven : 4 ≤ 7 :=
  open Nat.le in
  step (step (step refl))
def Nat.lt (n m : Nat) : Prop :=
  Nat.le (n + 1) m

instance : LT Nat where
  lt := Nat.lt
theorem four_lt_seven : 4 < 7 :=
  open Nat.le in
  step (step refl)
def Array.map (f : α → β) (arr : Array α) : Array β :=
  arrayMapHelper f arr Array.empty 0
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
termination_by arr.size - i
def Array.find (arr : Array α) (p : α → Bool) :
    Option (Nat × α) :=
  findHelper arr p 0
def findHelper (arr : Array α) (p : α → Bool)
    (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
def findHelper (arr : Array α) (p : α → Bool)
    (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
termination_by?