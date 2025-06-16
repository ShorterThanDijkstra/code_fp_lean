-- https://lean-lang.org/functional_programming_in_lean//Overloading-and-Type-Classes/Arrays-and-Indexing/#Functional-Programming-in-Lean--Overloading-and-Type-Classes--Arrays-and-Indexing
def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | {head := _, tail := []}, _ + 1 => none
  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail[n]?
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length
theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by⊢ idahoSpiders.inBounds 2 decideAll goals completed! 🐙

theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by⊢ ¬idahoSpiders.inBounds 5 decideAll goals completed! 🐙
def NonEmptyList.get (xs : NonEmptyList α)
    (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]
class GetElem
    (coll : Type)
    (idx : Type)
    (item : outParam Type)
    (inBounds : outParam (coll → idx → Prop)) where
  getElem : (c : coll) → (i : idx) → inBounds c i → item
instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get
instance : GetElem (List α) Pos α
    (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]
instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if not i then p.x else p.y