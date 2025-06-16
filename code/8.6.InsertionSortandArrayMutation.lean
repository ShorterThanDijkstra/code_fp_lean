-- https://lean-lang.org/functional_programming_in_lean//Programming___-Proving___-and-Performance/Insertion-Sort-and-Array-Mutation/#Functional-Programming-in-Lean--Programming___-Proving___-and-Performance--Insertion-Sort-and-Array-Mutation
#check dbgTraceIfShared
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := byα:Type ?u.26964inst✝:Ord αarr:Array αi:Fin arr.sizei':NatisLt✝:i' + 1 < arr.size⊢ i' < arr.size
      omegaAll goals completed! 🐙
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      insertSorted (arr.swap i' i) ⟨i', byα:Type ?u.26964inst✝:Ord αarr:Array αi:Fin arr.sizei':NatisLt✝:i' + 1 < arr.sizethis:i' < arr.size⊢ i' < (arr.swap i' (↑i) this ⋯).size simp [*]All goals completed! 🐙⟩
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
partial def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
#eval insertionSortLoop #[5, 17, 3, 8] 0
#eval insertionSortLoop #["metamorphic", "igneous", "sedentary"] 0
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := byα:Type ?u.125037inst✝:Ord αarr:Array αi:Nath:i < arr.size⊢ (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i
      sorryAll goals completed! 🐙
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := byα:Type u_1inst✝:Ord αarr:Array αi:Fin arr.size⊢ (insertSorted arr i).size = arr.size
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]All goals completed! 🐙
    | succ j' ih =>
      simp [insertSorted]succα:Type u_1inst✝:Ord αarr:Array αi:Fin arr.sizej':Natih:∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizeisLt:j' + 1 < arr.size⊢ (match compare arr[j'] arr[j' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size =
  arr.size
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := byα:Type u_1inst✝:Ord αarr:Array αi:Fin arr.size⊢ (insertSorted arr i).size = arr.size
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]All goals completed! 🐙
    | succ j' ih =>
      simp [insertSorted]succα:Type u_1inst✝:Ord αarr:Array αi:Fin arr.sizej':Natih:∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizeisLt:j' + 1 < arr.size⊢ (match compare arr[j'] arr[j' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size =
  arr.size
      splitsucc.h_1α:Type u_1inst✝:Ord αarr:Array αi:Fin arr.sizej':Natih:∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.lt⊢ arr.size = arr.sizesucc.h_2α:Type u_1inst✝:Ord αarr:Array αi:Fin arr.sizej':Natih:∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.eq⊢ arr.size = arr.sizesucc.h_3α:Type u_1inst✝:Ord αarr:Array αi:Fin arr.sizej':Natih:∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.gt⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := byα:Type u_1inst✝:Ord αarr:Array αi:Fin arr.size⊢ (insertSorted arr i).size = arr.size
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]All goals completed! 🐙
    | succ j' ih =>
      simp [insertSorted]succα:Type u_1inst✝:Ord αarr:Array αi:Fin arr.sizej':Natih:∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizeisLt:j' + 1 < arr.size⊢ (match compare arr[j'] arr[j' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size =
  arr.size
      splitsucc.h_1α:Type u_1inst✝:Ord αarr:Array αi:Fin arr.sizej':Natih:∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.lt⊢ arr.size = arr.sizesucc.h_2α:Type u_1inst✝:Ord αarr:Array αi:Fin arr.sizej':Natih:∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.eq⊢ arr.size = arr.sizesucc.h_3α:Type u_1inst✝:Ord αarr:Array αi:Fin arr.sizej':Natih:∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.gt⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size <;>succ.h_1α:Type u_1inst✝:Ord αarr:Array αi:Fin arr.sizej':Natih:∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.lt⊢ arr.size = arr.sizesucc.h_2α:Type u_1inst✝:Ord αarr:Array αi:Fin arr.sizej':Natih:∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.eq⊢ arr.size = arr.sizesucc.h_3α:Type u_1inst✝:Ord αarr:Array αi:Fin arr.sizej':Natih:∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.gt⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size try rflsucc.h_3α:Type u_1inst✝:Ord αarr:Array αi:Fin arr.sizej':Natih:∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.gt⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := byα:Type u_1inst✝:Ord αarr:Array αi:Fin arr.size⊢ (insertSorted arr i).size = arr.size
  match i with
  | ⟨j, isLt⟩ =>
    induction j generalizing arr with
    | zero => simp [insertSorted]All goals completed! 🐙
    | succ j' ih =>
      simp [insertSorted]succα:Type u_1inst✝:Ord αj':Natih:∀ (arr : Array α), Fin arr.size → ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizearr:Array αi:Fin arr.sizeisLt:j' + 1 < arr.size⊢ (match compare arr[j'] arr[j' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size =
  arr.size
      splitsucc.h_1α:Type u_1inst✝:Ord αj':Natih:∀ (arr : Array α), Fin arr.size → ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizearr:Array αi:Fin arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.lt⊢ arr.size = arr.sizesucc.h_2α:Type u_1inst✝:Ord αj':Natih:∀ (arr : Array α), Fin arr.size → ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizearr:Array αi:Fin arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.eq⊢ arr.size = arr.sizesucc.h_3α:Type u_1inst✝:Ord αj':Natih:∀ (arr : Array α), Fin arr.size → ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizearr:Array αi:Fin arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.gt⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size <;>succ.h_1α:Type u_1inst✝:Ord αj':Natih:∀ (arr : Array α), Fin arr.size → ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizearr:Array αi:Fin arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.lt⊢ arr.size = arr.sizesucc.h_2α:Type u_1inst✝:Ord αj':Natih:∀ (arr : Array α), Fin arr.size → ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizearr:Array αi:Fin arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.eq⊢ arr.size = arr.sizesucc.h_3α:Type u_1inst✝:Ord αj':Natih:∀ (arr : Array α), Fin arr.size → ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizearr:Array αi:Fin arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.gt⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size try rflsucc.h_3α:Type u_1inst✝:Ord αj':Natih:∀ (arr : Array α), Fin arr.size → ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.sizearr:Array αi:Fin arr.sizeisLt:j' + 1 < arr.sizex✝:Orderingheq✝:compare arr[j'] arr[j' + 1] = Ordering.gt⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
    (insertSorted arr ⟨i, isLt⟩).size = len := byα:Type u_1inst✝:Ord αlen:Nati:Nat⊢ ∀ (arr : Array α) (isLt : i < arr.size), arr.size = len → (insertSorted arr ⟨i, isLt⟩).size = len
  skipα:Type u_1inst✝:Ord αlen:Nati:Nat⊢ ∀ (arr : Array α) (isLt : i < arr.size), arr.size = len → (insertSorted arr ⟨i, isLt⟩).size = len
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
    (insertSorted arr ⟨i, isLt⟩).size = len := byα:Type u_1inst✝:Ord αlen:Nati:Nat⊢ ∀ (arr : Array α) (isLt : i < arr.size), arr.size = len → (insertSorted arr ⟨i, isLt⟩).size = len
  induction i with
  | zero => skipzeroα:Type u_1inst✝:Ord αlen:Nat⊢ ∀ (arr : Array α) (isLt : 0 < arr.size), arr.size = len → (insertSorted arr ⟨0, isLt⟩).size = len
  | succ i' ih => skipsuccα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = len⊢ ∀ (arr : Array α) (isLt : i' + 1 < arr.size), arr.size = len → (insertSorted arr ⟨i' + 1, isLt⟩).size = len
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
    (insertSorted arr ⟨i, isLt⟩).size = len := byα:Type u_1inst✝:Ord αlen:Nati:Nat⊢ ∀ (arr : Array α) (isLt : i < arr.size), arr.size = len → (insertSorted arr ⟨i, isLt⟩).size = len
  induction i with
  | zero =>
    intro arr isLt hLenzeroα:Type u_1inst✝:Ord αlen:Natarr:Array αisLt:0 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨0, isLt⟩).size = len
    simp [insertSorted]zeroα:Type u_1inst✝:Ord αlen:Natarr:Array αisLt:0 < arr.sizehLen:arr.size = len⊢ arr.size = len
  | succ i' ih => skipsuccα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = len⊢ ∀ (arr : Array α) (isLt : i' + 1 < arr.size), arr.size = len → (insertSorted arr ⟨i' + 1, isLt⟩).size = len
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
    (insertSorted arr ⟨i, isLt⟩).size = len := byα:Type u_1inst✝:Ord αlen:Nati:Nat⊢ ∀ (arr : Array α) (isLt : i < arr.size), arr.size = len → (insertSorted arr ⟨i, isLt⟩).size = len
  induction i with
  | zero =>
    intro arr isLt hLenzeroα:Type u_1inst✝:Ord αlen:Natarr:Array αisLt:0 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨0, isLt⟩).size = len
    simp [insertSorted, *]All goals completed! 🐙
  | succ i' ih => skipsuccα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = len⊢ ∀ (arr : Array α) (isLt : i' + 1 < arr.size), arr.size = len → (insertSorted arr ⟨i' + 1, isLt⟩).size = len
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := byα:Type u_1inst✝:Ord αlen:Nati:Nat⊢ ∀ (arr : Array α) (isLt : i < arr.size), arr.size = len → (insertSorted arr ⟨i, isLt⟩).size = len
  induction i with
  | zero =>
    intro arr isLt hLenzeroα:Type u_1inst✝:Ord αlen:Natarr:Array αisLt:0 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨0, isLt⟩).size = len
    simp [insertSorted, *]All goals completed! 🐙
  | succ i' ih =>
    intro arr isLt hLensuccα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨i' + 1, isLt⟩).size = len
    simp [insertSorted]succα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = len⊢ (match compare arr[i'] arr[i' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size =
  len
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := byα:Type u_1inst✝:Ord αlen:Nati:Nat⊢ ∀ (arr : Array α) (isLt : i < arr.size), arr.size = len → (insertSorted arr ⟨i, isLt⟩).size = len
  induction i with
  | zero =>
    intro arr isLt hLenzeroα:Type u_1inst✝:Ord αlen:Natarr:Array αisLt:0 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨0, isLt⟩).size = len
    simp [insertSorted, *]All goals completed! 🐙
  | succ i' ih =>
    intro arr isLt hLensuccα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨i' + 1, isLt⟩).size = len
    simp [insertSorted]succα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = len⊢ (match compare arr[i'] arr[i' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size =
  len
    splitsucc.h_1α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.lt⊢ arr.size = lensucc.h_2α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.eq⊢ arr.size = lensucc.h_3α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.gt⊢ (insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size = len
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := byα:Type u_1inst✝:Ord αlen:Nati:Nat⊢ ∀ (arr : Array α) (isLt : i < arr.size), arr.size = len → (insertSorted arr ⟨i, isLt⟩).size = len
  induction i with
  | zero =>
    intro arr isLt hLenzeroα:Type u_1inst✝:Ord αlen:Natarr:Array αisLt:0 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨0, isLt⟩).size = len
    simp [insertSorted, *]All goals completed! 🐙
  | succ i' ih =>
    intro arr isLt hLensuccα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨i' + 1, isLt⟩).size = len
    simp [insertSorted]succα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = len⊢ (match compare arr[i'] arr[i' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size =
  len
    splitsucc.h_1α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.lt⊢ arr.size = lensucc.h_2α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.eq⊢ arr.size = lensucc.h_3α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.gt⊢ (insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size = len <;>succ.h_1α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.lt⊢ arr.size = lensucc.h_2α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.eq⊢ arr.size = lensucc.h_3α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.gt⊢ (insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size = len try assumptionsucc.h_3α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.gt⊢ (insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size = len
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := byα:Type u_1inst✝:Ord αlen:Nati:Nat⊢ ∀ (arr : Array α) (isLt : i < arr.size), arr.size = len → (insertSorted arr ⟨i, isLt⟩).size = len
  induction i with
  | zero =>
    intro arr isLt hLenzeroα:Type u_1inst✝:Ord αlen:Natarr:Array αisLt:0 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨0, isLt⟩).size = len
    simp [insertSorted, *]All goals completed! 🐙
  | succ i' ih =>
    intro arr isLt hLensuccα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨i' + 1, isLt⟩).size = len
    simp [insertSorted]succα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = len⊢ (match compare arr[i'] arr[i' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size =
  len
    splitsucc.h_1α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.lt⊢ arr.size = lensucc.h_2α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.eq⊢ arr.size = lensucc.h_3α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.gt⊢ (insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size = len <;>succ.h_1α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.lt⊢ arr.size = lensucc.h_2α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.eq⊢ arr.size = lensucc.h_3α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.gt⊢ (insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size = len try assumptionsucc.h_3α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.gt⊢ (insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size = len
    simp [*]All goals completed! 🐙
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := byα:Type u_1inst✝:Ord αlen:Nati:Nat⊢ ∀ (arr : Array α) (isLt : i < arr.size), arr.size = len → (insertSorted arr ⟨i, isLt⟩).size = len
  induction i with
  | zero =>
    intro arr isLt hLenzeroα:Type u_1inst✝:Ord αlen:Natarr:Array αisLt:0 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨0, isLt⟩).size = len
    simp [insertSorted, *]All goals completed! 🐙
  | succ i' ih =>
    intro arr isLt hLensuccα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨i' + 1, isLt⟩).size = len
    simp [insertSorted]succα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = len⊢ (match compare arr[i'] arr[i' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size =
  len
    splitsucc.h_1α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.lt⊢ arr.size = lensucc.h_2α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.eq⊢ arr.size = lensucc.h_3α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.gt⊢ (insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size = len <;>succ.h_1α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.lt⊢ arr.size = lensucc.h_2α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.eq⊢ arr.size = lensucc.h_3α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.gt⊢ (insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size = len simp [*]All goals completed! 🐙
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := byα:Type ?u.130721inst✝:Ord αarr:Array αi:Nath:i < arr.size⊢ (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i
      rw [insert_sorted_size_eq arr.size i arr h rfl]α:Type ?u.130721inst✝:Ord αarr:Array αi:Nath:i < arr.size⊢ arr.size - (i + 1) < arr.size - i
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := byα:Type ?u.136577inst✝:Ord αarr:Array αi:Nath:i < arr.size⊢ (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i
      rw [insert_sorted_size_eq arr.size i arr h rfl]α:Type ?u.136577inst✝:Ord αarr:Array αi:Nath:i < arr.size⊢ arr.size - (i + 1) < arr.size - i
      omegaAll goals completed! 🐙
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
def insertionSort [Ord α] (arr : Array α) : Array α :=
   insertionSortLoop arr 0
#eval insertionSort #[3, 1, 7, 4]
#eval insertionSort #[ "quartz", "marble", "granite", "hematite"]
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := byα:Type ?u.13inst✝:Ord αarr:Array αi:Fin arr.sizei':NatisLt✝:i' + 1 < arr.size⊢ i' < arr.size
      omegaAll goals completed! 🐙
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      have : (dbgTraceIfShared "array to swap" arr).size = arr.size := byα:Type ?u.13inst✝:Ord αarr:Array αi:Fin arr.sizei':NatisLt✝:i' + 1 < arr.sizethis:i' < arr.size⊢ (dbgTraceIfShared "array to swap" arr).size = arr.size
        simp [dbgTraceIfShared]All goals completed! 🐙
      insertSorted
        ((dbgTraceIfShared "array to swap" arr).swap i' i)
        ⟨i', byα:Type ?u.13inst✝:Ord αarr:Array αi:Fin arr.sizei':NatisLt✝:i' + 1 < arr.sizethis✝:i' < arr.sizethis:(dbgTraceIfShared "array to swap" arr).size = arr.size⊢ i' < ((dbgTraceIfShared "array to swap" arr).swap i' (↑i) this✝ ⋯).size simp [*]All goals completed! 🐙⟩

theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := byα:Type u_1inst✝:Ord αlen:Nati:Nat⊢ ∀ (arr : Array α) (isLt : i < arr.size), arr.size = len → (insertSorted arr ⟨i, isLt⟩).size = len
  induction i with
  | zero =>
    intro arr isLt hLenzeroα:Type u_1inst✝:Ord αlen:Natarr:Array αisLt:0 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨0, isLt⟩).size = len
    simp [insertSorted, *]All goals completed! 🐙
  | succ i' ih =>
    intro arr isLt hLensuccα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = len⊢ (insertSorted arr ⟨i' + 1, isLt⟩).size = len
    simp [insertSorted, dbgTraceIfShared]succα:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = len⊢ (match compare arr[i'] arr[i' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size =
  len
    splitsucc.h_1α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.lt⊢ arr.size = lensucc.h_2α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.eq⊢ arr.size = lensucc.h_3α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.gt⊢ (insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size = len <;>succ.h_1α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.lt⊢ arr.size = lensucc.h_2α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.eq⊢ arr.size = lensucc.h_3α:Type u_1inst✝:Ord αlen:Nati':Natih:∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = lenarr:Array αisLt:i' + 1 < arr.sizehLen:arr.size = lenx✝:Orderingheq✝:compare arr[i'] arr[i' + 1] = Ordering.gt⊢ (insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size = len simp [*]All goals completed! 🐙

def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := byα:Type ?u.23008inst✝:Ord αarr:Array αi:Nath:i < arr.size⊢ (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i
      rw [insert_sorted_size_eq arr.size i arr h rfl]α:Type ?u.23008inst✝:Ord αarr:Array αi:Nath:i < arr.size⊢ arr.size - (i + 1) < arr.size - i
      omegaAll goals completed! 🐙
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i

def insertionSort [Ord α] (arr : Array α) : Array α :=
  insertionSortLoop arr 0
def getLines : IO (Array String) := do
  let stdin ← IO.getStdin
  let mut lines : Array String := #[]
  let mut currLine ← stdin.getLine
  while !currLine.isEmpty do
     -- Drop trailing newline:
    lines := lines.push (currLine.dropRight 1)
    currLine ← stdin.getLine
  pure lines
def mainUnique : IO Unit := do
  let lines ← getLines
  for line in insertionSort lines do
    IO.println line

def mainShared : IO Unit := do
  let lines ← getLines
  IO.println "--- Sorted lines: ---"
  for line in insertionSort lines do
    IO.println line

  IO.println ""
  IO.println "--- Original data: ---"
  for line in lines do
    IO.println line
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--shared"] => mainShared; pure 0
  | ["--unique"] => mainUnique; pure 0
  | _ =>
    IO.println "Expected single argument, either \"--shared\" or \"--unique\""
    pure 1