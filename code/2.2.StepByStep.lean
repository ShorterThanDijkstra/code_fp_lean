-- https://lean-lang.org/functional_programming_in_lean//Hello___-World___/Step-By-Step/#Functional-Programming-in-Lean--Hello___-World___--Step-By-Step
let stdin ← IO.getStdin
let stdout ← IO.getStdout
stdout.putStrLn "How would you like to be addressed?"
let input ← stdin.getLine
let name := input.dropRightWhile Char.isWhitespace
stdout.putStrLn s!"Hello, {name}!"
let stdout ← IO.getStdout
stdout.putStrLn "How would you like to be addressed?"
let input ← stdin.getLine
let name := input.dropRightWhile Char.isWhitespace
stdout.putStrLn s!"Hello, {name}!"
stdout.putStrLn "How would you like to be addressed?"
let input ← stdin.getLine
let name := input.dropRightWhile Char.isWhitespace
stdout.putStrLn s!"Hello, {name}!"
let name := input.dropRightWhile Char.isWhitespace
stdout.putStrLn s!"Hello, {name}!"
#eval "Hello!!!".dropRightWhile (· == '!')
#eval "Hello...   ".dropRightWhile (fun c => not (c.isAlphanum))
stdout.putStrLn s!"Hello, {name}!"
def twice (action : IO Unit) : IO Unit := do
  action
  action
twice (IO.println "shy")
def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n
def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n
def from5 : List (IO Unit) := countdown 5
#eval from5.length
def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions
def main : IO Unit := runActions from5
main
runActions from5
runActions (countdown 5)
runActions
  [IO.println "5",
   IO.println "4",
   IO.println "3",
   IO.println "2",
   IO.println "1",
   IO.println "Blast off!"]
do IO.println "5"
   IO.println "4"
   IO.println "3"
   IO.println "2"
   IO.println "1"
   IO.println "Blast off!"
   pure ()
def main : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting