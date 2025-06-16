-- https://lean-lang.org/functional_programming_in_lean//Hello___-World___/Running-a-Program/#running-a-program
def main : IO Unit := IO.println "Hello, world!"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"
def main : IO Unit := do
let stdin ← IO.getStdin
let stdout ← IO.getStdout
stdout.putStrLn "How would you like to be addressed?"
let input ← stdin.getLine
let name := input.dropRightWhile Char.isWhitespace
stdout.putStrLn s!"Hello, {name}!"