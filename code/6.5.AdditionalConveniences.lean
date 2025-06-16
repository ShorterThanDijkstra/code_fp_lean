-- https://lean-lang.org/functional_programming_in_lean//Monad-Transformers/Additional-Conveniences/#Functional-Programming-in-Lean--Monad-Transformers--Additional-Conveniences
#eval some 5 |> toString
def times3 (n : Nat) : Nat := n * 3
#eval 5 |> times3 |> toString |> ("It is " ++ ·)
#eval ("It is " ++ ·) <| toString <| times3 <| 5
#eval ("It is " ++ ·) (toString (times3 5))
def spam : IO Unit := do
  repeat IO.println "Spam!"
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream
def dump (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  repeat do
    let buf ← stream.read bufsize
    if buf.isEmpty then break
    stdout.write buf
def dump (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  let mut buf ← stream.read bufsize
  while not buf.isEmpty do
    stdout.write buf
    buf ← stream.read bufsize