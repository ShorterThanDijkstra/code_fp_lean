-- https://lean-lang.org/functional_programming_in_lean//Programming___-Proving___-and-Performance/Proving-Equivalence/#Functional-Programming-in-Lean--Programming___-Proving___-and-Performance--Proving-Equivalence
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by⊢ NonTail.sum = Tail.sum
  skip⊢ NonTail.sum = Tail.sum
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by⊢ NonTail.sum = Tail.sum
  funext xshxs:List Nat⊢ NonTail.sum xs = Tail.sum xs
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by⊢ NonTail.sum = Tail.sum
  funext xshxs:List Nat⊢ NonTail.sum xs = Tail.sum xs
  induction xs with
  | nil => skiph.nil⊢ NonTail.sum [] = Tail.sum []
  | cons y ys ih => skiph.consy:Natys:List Natih:NonTail.sum ys = Tail.sum ys⊢ NonTail.sum (y :: ys) = Tail.sum (y :: ys)
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by⊢ NonTail.sum = Tail.sum
  funext xshxs:List Nat⊢ NonTail.sum xs = Tail.sum xs
  induction xs with
  | nil => rflAll goals completed! 🐙
  | cons y ys ih => skiph.consy:Natys:List Natih:NonTail.sum ys = Tail.sum ys⊢ NonTail.sum (y :: ys) = Tail.sum (y :: ys)
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by⊢ NonTail.sum = Tail.sum
  funext xshxs:List Nat⊢ NonTail.sum xs = Tail.sum xs
  induction xs with
  | nil => rflAll goals completed! 🐙
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum]h.consy:Natys:List Natih:NonTail.sum ys = Tail.sum ys⊢ y + NonTail.sum ys = Tail.sumHelper 0 (y :: ys)
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by⊢ NonTail.sum = Tail.sum
  funext xshxs:List Nat⊢ NonTail.sum xs = Tail.sum xs
  induction xs with
  | nil => rflAll goals completed! 🐙
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum, Tail.sumHelper]h.consy:Natys:List Natih:NonTail.sum ys = Tail.sum ys⊢ y + NonTail.sum ys = Tail.sumHelper y ys
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by⊢ NonTail.sum = Tail.sum
  funext xshxs:List Nat⊢ NonTail.sum xs = Tail.sum xs
  induction xs with
  | nil => rflAll goals completed! 🐙
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum, Tail.sumHelper]h.consy:Natys:List Natih:NonTail.sum ys = Tail.sum ys⊢ y + NonTail.sum ys = Tail.sumHelper y ys
    rw [ih]h.consy:Natys:List Natih:NonTail.sum ys = Tail.sum ys⊢ y + Tail.sum ys = Tail.sumHelper y ys
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := byxs:List Natn:Nat⊢ n + Tail.sum xs = Tail.sumHelper n xs
  skipxs:List Natn:Nat⊢ n + Tail.sum xs = Tail.sumHelper n xs
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := byxs:List Natn:Nat⊢ n + Tail.sum xs = Tail.sumHelper n xs
  induction xs with
  | nil => rflAll goals completed! 🐙
  | cons y ys ih => skipconsn:Naty:Natys:List Natih:n + Tail.sum ys = Tail.sumHelper n ys⊢ n + Tail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := byxs:List Natn:Nat⊢ n + Tail.sum xs = Tail.sumHelper n xs
  induction xs with
  | nil => rflAll goals completed! 🐙
  | cons y ys ih =>
    simp [Tail.sum, Tail.sumHelper]consn:Naty:Natys:List Natih:n + Tail.sum ys = Tail.sumHelper n ys⊢ n + Tail.sumHelper y ys = Tail.sumHelper (y + n) ys
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := byxs:List Nat⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
  skipxs:List Nat⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := byxs:List Nat⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
  induction xs with
  | nil => skipnil⊢ ∀ (n : Nat), n + NonTail.sum [] = Tail.sumHelper n []
  | cons y ys ih => skipconsy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := byxs:List Nat⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
  induction xs with
  | nil => intro nniln:Nat⊢ n + NonTail.sum [] = Tail.sumHelper n []
  | cons y ys ih => skipconsy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := byxs:List Nat⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
  induction xs with
  | nil =>
    intro nniln:Nat⊢ n + NonTail.sum [] = Tail.sumHelper n []
    rflAll goals completed! 🐙
  | cons y ys ih => skipconsy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := byxs:List Nat⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
  induction xs with
  | nil =>
    intro nniln:Nat⊢ n + NonTail.sum [] = Tail.sumHelper n []
    rflAll goals completed! 🐙
  | cons y ys ih =>
    intro nconsy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := byxs:List Nat⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
  induction xs with
  | nil =>
    intro nniln:Nat⊢ n + NonTail.sum [] = Tail.sumHelper n []
    rflAll goals completed! 🐙
  | cons y ys ih =>
    intro nconsy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
    simp [NonTail.sum, Tail.sumHelper]consy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + (y + NonTail.sum ys) = Tail.sumHelper (y + n) ys
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := byxs:List Nat⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
  induction xs with
  | nil =>
    intro nniln:Nat⊢ n + NonTail.sum [] = Tail.sumHelper n []
    rflAll goals completed! 🐙
  | cons y ys ih =>
    intro nconsy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
    simp [NonTail.sum, Tail.sumHelper]consy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + (y + NonTail.sum ys) = Tail.sumHelper (y + n) ys
    rw [←Nat.add_assoc]consy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + y + NonTail.sum ys = Tail.sumHelper (y + n) ys
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := byxs:List Nat⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
  induction xs with
  | nil =>
    intro nniln:Nat⊢ n + NonTail.sum [] = Tail.sumHelper n []
    rflAll goals completed! 🐙
  | cons y ys ih =>
    intro nconsy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
    simp [NonTail.sum, Tail.sumHelper]consy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + (y + NonTail.sum ys) = Tail.sumHelper (y + n) ys
    rw [←Nat.add_assoc]consy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + y + NonTail.sum ys = Tail.sumHelper (y + n) ys
    rw [Nat.add_comm]consy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ NonTail.sum ys + (n + y) = Tail.sumHelper (y + n) ys
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := byxs:List Nat⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
  induction xs with
  | nil =>
    intro nniln:Nat⊢ n + NonTail.sum [] = Tail.sumHelper n []
    rflAll goals completed! 🐙
  | cons y ys ih =>
    intro nconsy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
    simp [NonTail.sum, Tail.sumHelper]consy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + (y + NonTail.sum ys) = Tail.sumHelper (y + n) ys
    rw [←Nat.add_assoc]consy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + y + NonTail.sum ys = Tail.sumHelper (y + n) ys
    rw [Nat.add_comm y n]consy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + y + NonTail.sum ys = Tail.sumHelper (n + y) ys
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := byxs:List Nat⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
  induction xs with
  | nil => intro nniln:Nat⊢ n + NonTail.sum [] = Tail.sumHelper n []; rflAll goals completed! 🐙
  | cons y ys ih =>
    intro nconsy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
    simp [NonTail.sum, Tail.sumHelper]consy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + (y + NonTail.sum ys) = Tail.sumHelper (y + n) ys
    rw [←Nat.add_assoc]consy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + y + NonTail.sum ys = Tail.sumHelper (y + n) ys
    rw [Nat.add_comm y n]consy:Natys:List Natih:∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ysn:Nat⊢ n + y + NonTail.sum ys = Tail.sumHelper (n + y) ys
    exact ih (n + y)All goals completed! 🐙
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by⊢ NonTail.sum = Tail.sum
  funext xshxs:List Nat⊢ NonTail.sum xs = Tail.sum xs
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by⊢ NonTail.sum = Tail.sum
  funext xshxs:List Nat⊢ NonTail.sum xs = Tail.sum xs
  simp [Tail.sum]hxs:List Nat⊢ NonTail.sum xs = Tail.sumHelper 0 xs
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by⊢ NonTail.sum = Tail.sum
  funext xshxs:List Nat⊢ NonTail.sum xs = Tail.sum xs
  simp [Tail.sum]hxs:List Nat⊢ NonTail.sum xs = Tail.sumHelper 0 xs
  rw [←Nat.zero_add (NonTail.sum xs)]hxs:List Nat⊢ 0 + NonTail.sum xs = Tail.sumHelper 0 xs
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by⊢ NonTail.sum = Tail.sum
  funext xshxs:List Nat⊢ NonTail.sum xs = Tail.sum xs
  simp [Tail.sum]hxs:List Nat⊢ NonTail.sum xs = Tail.sumHelper 0 xs
  rw [←Nat.zero_add (NonTail.sum xs)]hxs:List Nat⊢ 0 + NonTail.sum xs = Tail.sumHelper 0 xs
  exact non_tail_sum_eq_helper_accum xs 0All goals completed! 🐙
theorem non_tail_reverse_eq_tail_reverse :
    @NonTail.reverse = @Tail.reverse := by⊢ @NonTail.reverse = @Tail.reverse
  funext α xsh.hα:Type u_1xs:List α⊢ NonTail.reverse xs = Tail.reverse xs