namespace Algorithms.InsertionSort.Correctness

/-- A list is sorted when each element is at most every element after it. -/
def Sorted (xs : List Nat) : Prop := xs.Pairwise (· ≤ ·)

/-- A sorting implementation is correct when its output is sorted and is a
permutation of its input. -/
def Correct (impl : List Nat → List Nat) : Prop :=
  ∀ xs, Sorted (impl xs) ∧ (impl xs).Perm xs

end Algorithms.InsertionSort.Correctness
