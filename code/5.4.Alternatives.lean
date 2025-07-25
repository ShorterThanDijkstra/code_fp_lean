-- https://lean-lang.org/functional_programming_in_lean//Functors___-Applicative-Functors___-and-Monads/Alternatives/#alternative
abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) →
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970}) →
    NonEmptyString →
    LegacyCheckedInput
  | company :
    NonEmptyString →
    LegacyCheckedInput
deriving Repr
def Validate.orElse
    (a : Validate ε α)
    (b : Unit → Validate ε α) :
    Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)
class OrElse (α : Type) where
  orElse : α → (Unit → α) → α
instance : OrElse (Validate ε α) where
  orElse := Validate.orElse
def checkThat (condition : Bool)
    (field : Field) (msg : String) :
    Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg
def checkCompany (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  pure (fun () name => .company name) <*>
    checkThat (input.birthYear == "FIRM")
      "birth year" "FIRM if a company" <*>
    checkName input.name
class SeqRight (f : Type → Type) where
  seqRight : f α → (Unit → f β) → f β
def checkCompany (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM")
    "birth year" "FIRM if a company" *>
  pure .company <*> checkName input.name
def checkCompany (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM")
    "birth year" "FIRM if a company" *>
  .company <$> checkName input.name
def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)]
    (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }
def checkHumanBefore1970 (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970)
        ("birth year", "less than 1970") <*>
      pure input.name
def checkHumanAfter1970 (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970)
        ("birth year", "greater than 1970") <*>
      checkName input.name
def checkLegacyInput (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|>
  checkHumanBefore1970 input <|>
  checkHumanAfter1970 input
#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkLegacyInput ⟨"Johnny", "1963"⟩
#eval checkLegacyInput ⟨"", "1963"⟩
#eval checkLegacyInput ⟨"", "1970"⟩
class Alternative (f : Type → Type) extends Applicative f where
  failure : f α
  orElse : f α → (Unit → f α) → f α
instance [Alternative f] : OrElse (f α) where
  orElse := Alternative.orElse
instance : Alternative Option where
  failure := none
  orElse
    | some x, _ => some x
    | none, y => y ()
def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, ys => ys ()
  | .more x xs, ys => .more x (fun () => orElse (xs ()) ys)

instance : Alternative Many where
  failure := .none
  orElse := Many.orElse
def guard [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then
    pure ()
  else failure
def Many.countdown : Nat → Many Nat
  | 0 => .none
  | n + 1 => .more n (fun () => countdown n)

def evenDivisors (n : Nat) : Many Nat := do
  let k ← Many.countdown (n + 1)
  guard (k % 2 = 0)
  guard (n % k = 0)
  pure k
#eval (evenDivisors 20).takeAll
inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := .both