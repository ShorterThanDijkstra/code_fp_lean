-- https://lean-lang.org/functional_programming_in_lean//Overloading-and-Type-Classes/Standard-Classes/#Functional-Programming-in-Lean--Overloading-and-Type-Classes--Standard-Classes
#check 2 < 4
instance : LT Pos where
  lt x y := LT.lt x.toNat y.toNat
instance : LE Pos where
  le x y := LE.le x.toNat y.toNat
instance {x : Pos} {y : Pos} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))

instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat ≤ y.toNat))
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))
inductive Ordering where
  | lt
  | eq
  | gt
def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k

instance : Ord Pos where
  compare := Pos.comp
class Hashable (α : Type) where
  hash : α → UInt64
def hashPos : Pos → UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos
instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf =>
    0
  | BinTree.branch left x right =>
    mixHash 1
      (mixHash (hashBinTree left)
        (mixHash (hash x)
          (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree
deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable for NonEmptyList
class HAppend (α : Type) (β : Type) (γ : outParam Type) where
  hAppend : α → β → γ
instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }
#eval idahoSpiders ++ idahoSpiders
instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys :=
    { head := xs.head, tail := xs.tail ++ ys }
#eval idahoSpiders ++ ["Trapdoor Spider"]
instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }
instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }
def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail
class Functor (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β

  mapConst {α β : Type} (x : α) (coll : f β) : f α :=
    map (fun _ => x) coll
deriving instance ToString for NonEmptyList