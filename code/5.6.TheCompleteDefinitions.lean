-- https://lean-lang.org/functional_programming_in_lean//Functors___-Applicative-Functors___-and-Monads/The-Complete-Definitions/#Functional-Programming-in-Lean--Functors___-Applicative-Functors___-and-Monads--The-Complete-Definitions
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α :=
    Function.comp map (Function.const _)
def simpleConst  (x : α) (_ : β) : α := x
#eval [1, 2, 3].map (simpleConst "same")
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
inductive Functor (f : Type u → Type v) : Type (max (u+1) v) where
  | mk : ({α β : Type u} → (α → β) → f α → f β) → Functor f
class Pure (f : Type u → Type v) : Type (max (u+1) v) where
  pure {α : Type u} : α → f α
class Seq (f : Type u → Type v) : Type (max (u+1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
class SeqRight (f : Type u → Type v) : Type (max (u+1) v) where
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β
class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α
class Applicative (f : Type u → Type v)
    extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map      := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
Seq.seq (Functor.map (Function.const _) a) b
fun a b => Seq.seq ((fun x _ => x) <$> a) b
fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
fun a b => Seq.seq ((fun _ => id) <$> a) b
fun a b => Seq.seq ((fun _ => fun x => x) <$> a) b
fun a b => Seq.seq ((fun _ x => x) <$> a) b
class Bind (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β
class Monad (m : Type u → Type v) : Type (max (u+1) v)
    extends Applicative m, Bind m where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y (x ())
  seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()