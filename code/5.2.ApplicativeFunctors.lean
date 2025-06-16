-- https://lean-lang.org/functional_programming_in_lean//Functors___-Applicative-Functors___-and-Monads/Applicative-Functors/#Functional-Programming-in-Lean--Functors___-Applicative-Functors___-and-Monads--Applicative-Functors
instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()
instance : Applicative (Except ε) where
  pure x := .ok x
  seq f x :=
    match f with
    | .error e => .error e
    | .ok g => g <$> x ()
structure Pair (α β : Type) : Type where
  first : α
  second : β
instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩
id <$> Pair.mk x y
Pair.mk x (id y)
Pair.mk x y
f <$> g <$> Pair.mk x y
f <$> Pair.mk x (g y)
Pair.mk x (f (g y))
(f ∘ g) <$> Pair.mk x y
Pair.mk x ((f ∘ g) y)
Pair.mk x (f (g y))
def Pair.pure (x : β) : Pair α β := _
def Pair.pure (x : β) : Pair α β := Pair.mk _ x
structure RawInput where
  name : String
  birthYear : String
structure Subtype {α : Type} (p : α → Prop) where
  val : α
  property : p val
def FastPos : Type := {x : Nat // x > 0}
def one : FastPos := ⟨1, by⊢ 1 > 0 decideAll goals completed! 🐙⟩
instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, byn:Nat⊢ n + 1 > 0 simpAll goals completed! 🐙⟩
def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else none
structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}
inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
instance : Functor (Validate ε) where
  map f
   | .ok x => .ok (f x)
   | .errors errs => .errors errs
instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')
def Field := String
def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }
def checkName (name : String) :
    Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩
def Validate.andThen (val : Validate ε α)
    (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x
def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n
def checkBirthYear (thisYear year : Nat) :
    Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, bythisYear:Natyear:Nath:year > 1900h':year ≤ thisYear⊢ year > 1900 ∧ year ≤ thisYear simp [*]All goals completed! 🐙⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"
def checkInput (year : Nat) (input : RawInput) :
    Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
      checkBirthYear year birthYearAsNat
#eval checkInput 2023 {name := "David", birthYear := "1984"}
#eval checkInput 2023 {name := "", birthYear := "2045"}
#eval checkInput 2023 {name := "David", birthYear := "syzygy"}