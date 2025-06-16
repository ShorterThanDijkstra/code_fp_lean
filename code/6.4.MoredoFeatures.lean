-- https://lean-lang.org/functional_programming_in_lean//Monad-Transformers/More-do-Features/#Functional-Programming-in-Lean--Monad-Transformers--More-do-Features
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
      else throw (.notALetter c)
      loop cs
  loop str.toList
def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    if ← p x then
      modify (· + 1)
    count p xs
def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    unless ← p x do
      modify (· + 1)
    countNot p xs
def List.find? (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs =>
    if p x then
      some x
    else
      find? p xs
def List.find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs => do
    if p x then return x
    find? p xs
def runCatch [Monad m] (action : ExceptT α m α) : m α := do
  match ← action with
  | Except.ok x => pure x
  | Except.error x => pure x
def List.find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs =>
    runCatch do
      if p x then throw x else pure ()
      monadLift (find? p xs)
def main (argv : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  unless argv == [] do
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    return 1

  stdout.putStrLn "How would you like to be addressed?"
  stdout.flush

  let name := (← stdin.getLine).trim
  if name == "" then
    stderr.putStrLn s!"No name provided"
    return 1

  stdout.putStrLn s!"Hello, {name}!"

  return 0
def main (argv : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  if argv != [] then
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    pure 1
  else
    stdout.putStrLn "How would you like to be addressed?"
    stdout.flush

    let name := (← stdin.getLine).trim
    if name == "" then
      stderr.putStrLn s!"No name provided"
      pure 1
    else
      stdout.putStrLn s!"Hello, {name}!"
      pure 0
def greet (name : String) : String :=
  "Hello, " ++ Id.run do return name
class ForM (m : Type u → Type v) (γ : Type w₁)
    (α : outParam (Type w₂)) where
  forM [Monad m] : γ → (α → m PUnit) → m PUnit
def List.forM [Monad m] : List α → (α → m PUnit) → m PUnit
  | [], _ => pure ()
  | x :: xs, action => do
    action x
    forM xs action

instance : ForM m (List α) α where
  forM := List.forM
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  forM str.toList fun c => do
    if c.isAlpha then
      if vowels.contains c then
        modify fun st => {st with vowels := st.vowels + 1}
      else if consonants.contains c then
        modify fun st => {st with consonants := st.consonants + 1}
    else throw (.notALetter c)
def Many.forM [Monad m] : Many α → (α → m PUnit) → m PUnit
  | Many.none, _ => pure ()
  | Many.more first rest, action => do
    action first
    forM (rest ()) action

instance : ForM m (Many α) α where
  forM := Many.forM
structure AllLessThan where
  num : Nat
def AllLessThan.forM [Monad m]
    (coll : AllLessThan) (action : Nat → m Unit) :
    m Unit :=
  let rec countdown : Nat → m Unit
    | 0 => pure ()
    | n + 1 => do
      action n
      countdown n
  countdown coll.num

instance : ForM m AllLessThan Nat where
  forM := AllLessThan.forM
#eval forM { num := 5 : AllLessThan } IO.println
structure LinesOf where
  stream : IO.FS.Stream

partial def LinesOf.forM
    (readFrom : LinesOf) (action : String → IO Unit) :
    IO Unit := do
  let line ← readFrom.stream.getLine
  if line == "" then return ()
  action line
  forM readFrom action

instance : ForM IO LinesOf String where
  forM := LinesOf.forM
def main (argv : List String) : IO UInt32 := do
  if argv != [] then
    IO.eprintln "Unexpected arguments"
    return 1

  forM (LinesOf.mk (← IO.getStdin)) fun line => do
    if line.any (·.isAlpha) then
      IO.print line

  return 0
def OptionT.exec [Applicative m] (action : OptionT m α) : m Unit :=
  action *> pure ()
def countToThree (n : Nat) : IO Unit :=
  let nums : AllLessThan := ⟨n⟩
  OptionT.exec (forM nums fun i => do
    if i < 3 then failure else IO.println i)
#eval countToThree 7
def countToThree (n : Nat) : IO Unit := do
  let nums : AllLessThan := ⟨n⟩
  for i in nums do
    if i < 3 then break
    IO.println i
#eval countToThree 7
instance : ForIn m AllLessThan Nat where
  forIn := ForM.forIn
def List.find? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if p x then return x
  failure
def List.find? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if not (p x) then continue
    return x
  failure
def fourToEight : IO Unit := do
  for i in [4:9:2] do
    IO.println i
def parallelLoop := do
  for x in ["currant", "gooseberry", "rowan"], y in [4:8] do
    IO.println (x, y)
#eval parallelLoop
def printArray [ToString α] (xs : Array α) : IO Unit := do
  for h : i in [0:xs.size] do
    IO.println s!"{i}:\t{xs[i]}"
def two : Nat := Id.run do
  let mut x := 0
  x := x + 1
  x := x + 1
  return x
def two : Nat :=
  let block : StateT Nat Id Nat := do
    modify (· + 1)
    modify (· + 1)
    return (← get)
  let (result, _finalState) := block 0
  result
def three : Nat := Id.run do
  let mut x := 0
  for _ in [1, 2, 3] do
    x := x + 1
  return x
def six : Nat := Id.run do
  let mut x := 0
  for y in [1, 2, 3] do
    x := x + y
  return x
def List.count (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  for x in xs do
    if p x then found := found + 1
  return found
def List.count (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  let rec go : List α → Id Unit
    | [] => pure ()
    | y :: ys => do
      if p y then found := found + 1
      go ys
  return found
example : Id Unit := do
  let mut x := 0
  x := x + 1
example : Id Unit := do
  let mut x := 0
  let other := do
    x := x + 1
  other
example : Id Unit := do
  let mut x := 0
  let other ← do
    x := x + 1
  pure other
example : Id Unit := do
  let mut x := 0
  let addFour (y : Id Nat) := Id.run y + 4
  addFour do
    x := 5
example : Id Unit := do
  let mut x := 0
  do x := x + 1
example : Id Unit := do
  let mut x := 0
  if x > 2 then
    x := x + 1
example : Id Unit := do
  let mut x := 0
  if x > 2 then do
    x := x + 1
example : Id Unit := do
  let mut x := 0
  match true with
  | true => x := x + 1
  | false => x := 17
example : Id Unit := do
  let mut x := 0
  match true with
  | true => do
    x := x + 1
  | false => do
    x := 17
example : Id Unit := do
  let mut x := 0
  for y in [1:5] do
   x := x + y
example : Id Unit := do
  let mut x := 0
  unless 1 < 5 do
    x := x + 1