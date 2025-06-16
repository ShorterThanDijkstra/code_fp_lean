-- https://lean-lang.org/functional_programming_in_lean//Programming___-Proving___-and-Performance/More-Inequalities/#Functional-Programming-in-Lean--Programming___-Proving___-and-Performance--More-Inequalities
def merge [Ord α] (xs : List α) (ys : List α) : List α :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x'::xs', y'::ys' =>
    match Ord.compare x' y' with
    | .lt | .eq => x' :: merge xs' (y' :: ys')
    | .gt => y' :: merge (x'::xs') ys'
def splitList (lst : List α) : (List α × List α) :=
  match lst with
  | [] => ([], [])
  | x :: xs =>
    let (a, b) := splitList xs
    (x :: b, a)
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    merge (mergeSort halves.fst) (mergeSort halves.snd)
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := byα:Type u_1lst:List α⊢ (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length
  skipα:Type u_1lst:List α⊢ (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := byα:Type u_1lst:List α⊢ (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length
  induction lst with
  | nil => skipnilα:Type u_1⊢ (splitList []).fst.length ≤ [].length ∧ (splitList []).snd.length ≤ [].length
  | cons x xs ih => skipconsα:Type u_1x:αxs:List αih:(splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length⊢ (splitList (x :: xs)).fst.length ≤ (x :: xs).length ∧ (splitList (x :: xs)).snd.length ≤ (x :: xs).length
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := byα:Type u_1lst:List α⊢ (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length
  induction lst with
  | nil => simp [splitList]All goals completed! 🐙
  | cons x xs ih =>
    simp [splitList]consα:Type u_1x:αxs:List αih:(splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := byα:Type u_1lst:List α⊢ (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length
  induction lst with
  | nil => simp [splitList]All goals completed! 🐙
  | cons x xs ih =>
    simp [splitList]consα:Type u_1x:αxs:List αih:(splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
    cases ihcons.introα:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := byα:Type u_1lst:List α⊢ (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length
  induction lst with
  | nil => simp [splitList]All goals completed! 🐙
  | cons x xs ih =>
    simp [splitList]consα:Type u_1x:αxs:List αih:(splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
    cases ihcons.introα:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
    constructorcons.intro.leftα:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.lengthcons.intro.rightα:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).fst.length ≤ xs.length + 1
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := byα:Type u_1lst:List α⊢ (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length
  induction lst with
  | nil => simp [splitList]All goals completed! 🐙
  | cons x xs ih =>
    simp [splitList]consα:Type u_1x:αxs:List αih:(splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
    cases ihcons.introα:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
    constructorcons.intro.leftα:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.lengthcons.intro.rightα:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).fst.length ≤ xs.length + 1
    case left =>α:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.length assumptionAll goals completed! 🐙
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := byn:Natm:Nat⊢ n ≤ m → n ≤ m + 1
  skipn:Natm:Nat⊢ n ≤ m → n ≤ m + 1
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := byn:Natm:Nat⊢ n ≤ m → n ≤ m + 1
  intro hn:Natm:Nath:n ≤ m⊢ n ≤ m + 1
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := byn:Natm:Nat⊢ n ≤ m → n ≤ m + 1
  intro hn:Natm:Nath:n ≤ m⊢ n ≤ m + 1
  induction h with
  | refl => skiprefln:Natm:Nat⊢ n ≤ n + 1
  | step _ ih => skipstepn:Natm:Natm✝:Nata✝:n.le m✝ih:n ≤ m✝ + 1⊢ n ≤ m✝.succ + 1
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := byn:Natm:Nat⊢ n ≤ m → n ≤ m + 1
  intro hn:Natm:Nath:n ≤ m⊢ n ≤ m + 1
  induction h with
  | refl => constructorrefl.an:Natm:Nat⊢ n.le n
  | step _ ih => skipstepn:Natm:Natm✝:Nata✝:n.le m✝ih:n ≤ m✝ + 1⊢ n ≤ m✝.succ + 1
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := byn:Natm:Nat⊢ n ≤ m → n ≤ m + 1
  intro hn:Natm:Nath:n ≤ m⊢ n ≤ m + 1
  induction h with
  | refl => constructorrefl.an:Natm:Nat⊢ n.le n; constructorAll goals completed! 🐙
  | step _ ih => skipstepn:Natm:Natm✝:Nata✝:n.le m✝ih:n ≤ m✝ + 1⊢ n ≤ m✝.succ + 1
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := byn:Natm:Nat⊢ n ≤ m → n ≤ m + 1
  intro hn:Natm:Nath:n ≤ m⊢ n ≤ m + 1
  induction h with
  | refl => constructorrefl.an:Natm:Nat⊢ n.le n; constructorAll goals completed! 🐙
  | step _ ih => constructorstep.an:Natm:Natm✝:Nata✝:n.le m✝ih:n ≤ m✝ + 1⊢ n.le (m✝ + 1)
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := byn:Natm:Nat⊢ n ≤ m → n ≤ m + 1
  intro hn:Natm:Nath:n ≤ m⊢ n ≤ m + 1
  induction h with
  | refl => constructorrefl.an:Natm:Nat⊢ n.le n; constructorAll goals completed! 🐙
  | step => constructorstep.an:Natm:Natm✝:Nata✝:n.le m✝a_ih✝:n ≤ m✝ + 1⊢ n.le (m✝ + 1); assumptionAll goals completed! 🐙
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := byn:Natm:Nat⊢ n ≤ m → n ≤ m + 1
  intro hn:Natm:Nath:n ≤ m⊢ n ≤ m + 1
  induction h with
  | refl => apply Nat.le.steprefl.an:Natm:Nat⊢ n.le n; exact Nat.le.reflAll goals completed! 🐙
  | step _ ih => apply Nat.le.stepstep.an:Natm:Natm✝:Nata✝:n.le m✝ih:n ≤ m✝ + 1⊢ n.le (m✝ + 1); exact ihAll goals completed! 🐙
theorem Nat.le_succ_of_le (h : n ≤ m) : n ≤ m + 1:= byn:Natm:Nath:n ≤ m⊢ n ≤ m + 1
  induction hrefln:Natm:Nat⊢ n ≤ n + 1stepn:Natm:Natm✝:Nata✝:n.le m✝a_ih✝:n ≤ m✝ + 1⊢ n ≤ m✝.succ + 1 <;>refln:Natm:Nat⊢ n ≤ n + 1stepn:Natm:Natm✝:Nata✝:n.le m✝a_ih✝:n ≤ m✝ + 1⊢ n ≤ m✝.succ + 1 repeat (first | constructorstep.a.an:Natm:Natm✝:Nata✝:n.le m✝a_ih✝:n ≤ m✝ + 1⊢ n.le m✝ | assumptionAll goals completed! 🐙)
theorem Nat.le_succ_of_le (h : n ≤ m) : n ≤ m + 1:= byn:Natm:Nath:n ≤ m⊢ n ≤ m + 1
  omegaAll goals completed! 🐙
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1
  | .refl => .step .refl
  | .step h => .step (Nat.le_succ_of_le h)
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := byα:Type u_1lst:List α⊢ (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length
  induction lst with
  | nil => simp [splitList]All goals completed! 🐙
  | cons x xs ih =>
    simp [splitList]consα:Type u_1x:αxs:List αih:(splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
    cases ihcons.introα:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
    constructorcons.intro.leftα:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.lengthcons.intro.rightα:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).fst.length ≤ xs.length + 1
    case left =>α:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).snd.length ≤ xs.length assumptionAll goals completed! 🐙
    case right =>α:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).fst.length ≤ xs.length + 1
      apply Nat.le_succ_of_lehα:Type u_1x:αxs:List αleft✝:(splitList xs).fst.length ≤ xs.lengthright✝:(splitList xs).snd.length ≤ xs.length⊢ (splitList xs).fst.length ≤ xs.length
      assumptionAll goals completed! 🐙
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := byα:Type u_1lst:List αx✝:lst.length ≥ 2⊢ (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length
  skipα:Type u_1lst:List αx✝:lst.length ≥ 2⊢ (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := byα:Type u_1lst:List αx✝:lst.length ≥ 2⊢ (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length
  match lst with
  | x :: y :: xs =>
    skipα:Type u_1lst:List αx:αy:αxs:List αx✝:(x :: y :: xs).length ≥ 2⊢ (splitList (x :: y :: xs)).fst.length < (x :: y :: xs).length ∧
  (splitList (x :: y :: xs)).snd.length < (x :: y :: xs).length
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := byα:Type u_1lst:List αx✝:lst.length ≥ 2⊢ (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length
  match lst with
  | x :: y :: xs =>
    simp [splitList]α:Type u_1lst:List αx:αy:αxs:List αx✝:(x :: y :: xs).length ≥ 2⊢ (splitList xs).fst.length < xs.length + 1 ∧ (splitList xs).snd.length < xs.length + 1
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := byα:Type u_1lst:List αx✝:lst.length ≥ 2⊢ (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length
  match lst with
  | x :: y :: xs =>
    simp +arith [splitList]α:Type u_1lst:List αx:αy:αxs:List αx✝:(x :: y :: xs).length ≥ 2⊢ (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := byα:Type u_1lst:List αx✝:lst.length ≥ 2⊢ (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length
  match lst with
  | x :: y :: xs =>
    simp +arith [splitList]α:Type u_1lst:List αx:αy:αxs:List αx✝:(x :: y :: xs).length ≥ 2⊢ (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
    apply splitList_shorter_leAll goals completed! 🐙
theorem splitList_shorter_fst (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length :=
  splitList_shorter lst h |>.left

theorem splitList_shorter_snd (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).snd.length < lst.length :=
  splitList_shorter lst h |>.right
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : halves.fst.length < xs.length := byα:Type ?u.44291inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xs⊢ halves.fst.length < xs.length
      sorryAll goals completed! 🐙
    have : halves.snd.length < xs.length := byα:Type ?u.44291inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xsthis:halves.fst.length < xs.length⊢ halves.snd.length < xs.length
      sorryAll goals completed! 🐙
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : halves.fst.length < xs.length := byα:Type ?u.55173inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xs⊢ halves.fst.length < xs.length
      apply splitList_shorter_fsthα:Type ?u.55173inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xs⊢ xs.length ≥ 2
    have : halves.snd.length < xs.length := byα:Type ?u.55173inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xsthis:halves.fst.length < xs.length⊢ halves.snd.length < xs.length
      apply splitList_shorter_sndhα:Type ?u.55173inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xsthis:halves.fst.length < xs.length⊢ xs.length ≥ 2
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : xs.length ≥ 2 := byα:Type ?u.66107inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xs⊢ xs.length ≥ 2 sorryAll goals completed! 🐙
    have : halves.fst.length < xs.length := byα:Type ?u.66107inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xsthis:xs.length ≥ 2⊢ halves.fst.length < xs.length
      apply splitList_shorter_fsthα:Type ?u.66107inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xsthis:xs.length ≥ 2⊢ xs.length ≥ 2
      assumptionAll goals completed! 🐙
    have : halves.snd.length < xs.length := byα:Type ?u.66107inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xsthis✝:xs.length ≥ 2this:halves.fst.length < xs.length⊢ halves.snd.length < xs.length
      apply splitList_shorter_sndhα:Type ?u.66107inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xsthis✝:xs.length ≥ 2this:halves.fst.length < xs.length⊢ xs.length ≥ 2
      assumptionAll goals completed! 🐙
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : xs.length ≥ 2 := byα:Type ?u.77148inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xs⊢ xs.length ≥ 2
      omegaAll goals completed! 🐙
    have : halves.fst.length < xs.length := byα:Type ?u.77148inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xsthis:xs.length ≥ 2⊢ halves.fst.length < xs.length
      apply splitList_shorter_fsthα:Type ?u.77148inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xsthis:xs.length ≥ 2⊢ xs.length ≥ 2
      assumptionAll goals completed! 🐙
    have : halves.snd.length < xs.length := byα:Type ?u.77148inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xsthis✝:xs.length ≥ 2this:halves.fst.length < xs.length⊢ halves.snd.length < xs.length
      apply splitList_shorter_sndhα:Type ?u.77148inst✝:Ord αxs:List αh:¬xs.length < 2halves:List α × List α := splitList xsthis✝:xs.length ≥ 2this:halves.fst.length < xs.length⊢ xs.length ≥ 2
      assumptionAll goals completed! 🐙
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
#eval mergeSort ["soapstone", "geode", "mica", "limestone"]
#eval mergeSort [5, 3, 22, 15]
def div (n k : Nat) : Nat :=
  if n < k then
    0
  else
    1 + div (n - k) k
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok
termination_by n