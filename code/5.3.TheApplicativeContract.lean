-- https://lean-lang.org/functional_programming_in_lean//Functors___-Applicative-Functors___-and-Monads/The-Applicative-Contract/#Functional-Programming-in-Lean--Functors___-Applicative-Functors___-and-Monads--The-Applicative-Contract
some (· ∘ ·) <*> some f <*> some g <*> some x
some (f ∘ ·) <*> some g <*> some x
some (f ∘ g) <*> some x
some ((f ∘ g) x)
some (f (g x))
some f <*> (some g <*> some x)
some f <*> (some (g x))
some (f (g x))
some f <*> some x
f <$> some x
some (f x)
def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x
class Applicative (f : Type → Type) extends Functor f where
  pure : α → f α
  seq : f (α → β) → (Unit → f α) → f β
  map g x := seq (pure g) (fun () => x)
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure (g y)
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  f >>= fun g =>
  x () >>= fun y =>
  pure (g y)
pure id >>= fun g => v >>= fun y => pure (g y)
v >>= fun y => pure (id y)
v >>= fun y => pure y
v >>= pure
v
seq (seq (seq (pure (· ∘ ·)) (fun _ => u))
      (fun _ => v))
  (fun _ => w)
((pure (· ∘ ·) >>= fun f =>
   u >>= fun x =>
   pure (f x)) >>= fun g =>
  v >>= fun y =>
  pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
((u >>= fun x =>
   pure (x ∘ ·)) >>= fun g =>
   v >>= fun y =>
  pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
((u >>= fun x =>
   pure (x ∘ ·)) >>= (fun g =>
   v >>= fun y =>
  pure (g y))) >>= fun h =>
 w >>= fun z =>
 pure (h z)
(u >>= fun x =>
  pure (x ∘ ·) >>= fun g =>
 v  >>= fun y => pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
(u >>= fun x =>
  v >>= fun y =>
  pure (x ∘ y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
u >>= fun x =>
v >>= fun y =>
pure (x ∘ y) >>= fun h =>
w >>= fun z =>
pure (h z)
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure ((x ∘ y) z)
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure (x (y z))
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure (y z) >>= fun q =>
pure (x q)
u >>= fun x =>
v >>= fun y =>
 (w >>= fun p =>
  pure (y p)) >>= fun q =>
 pure (x q)
u >>= fun x =>
 (v >>= fun y =>
  w >>= fun q =>
  pure (y q)) >>= fun z =>
 pure (x z)
u >>= fun x =>
seq v (fun () => w) >>= fun q =>
pure (x q)
seq u (fun () => seq v (fun () => w))
seq (pure f) (fun () => pure x)
pure f >>= fun g =>
pure x >>= fun y =>
pure (g y)
pure f >>= fun g =>
pure (g x)
pure (f x)
seq u (fun () => pure x)
u >>= fun f =>
pure x >>= fun y =>
pure (f y)
u >>= fun f =>
pure (f x)
u >>= fun f =>
pure ((fun g => g x) f)
pure (fun g => g x) >>= fun h =>
u >>= fun f =>
pure (h f)
seq (pure (fun f => f x)) (fun () => u)
class Monad (m : Type → Type) extends Applicative m where
  bind : m α → (α → m β) → m β
  seq f x :=
    bind f fun g =>
    bind (x ()) fun y =>
    pure (g y)
def notFun : Validate String (Nat → String) :=
  .errors { head := "First error", tail := [] }

def notArg : Validate String Nat :=
  .errors { head := "Second error", tail := [] }
notFun <*> notArg
match notFun with
| .ok g => g <$> notArg
| .errors errs =>
  match notArg with
  | .ok _ => .errors errs
  | .errors errs' => .errors (errs ++ errs')
match notArg with
| .ok _ =>
  .errors { head := "First error", tail := [] }
| .errors errs' =>
  .errors ({ head := "First error", tail := [] } ++ errs')
.errors
  ({ head := "First error", tail := [] } ++
   { head := "Second error", tail := []})
.errors {
  head := "First error",
  tail := ["Second error"]
}
seq notFun (fun () => notArg)
notFun.andThen fun g =>
notArg.andThen fun y =>
pure (g y)
match notFun with
| .errors errs => .errors errs
| .ok val =>
  (fun g =>
    notArg.andThen fun y =>
    pure (g y)) val
.errors { head := "First error", tail := [] }