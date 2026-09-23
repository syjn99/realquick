/-!
Specification of lower-bound binary search over `Array Nat`.
-/

namespace Algorithms.BinarySearch.Correctness

/-- `a` is sorted in nondecreasing order: `a[i] ≤ a[j]` whenever `i < j`. -/
def Sorted (a : Array Nat) : Prop :=
  ∀ i j (hij : i < j) (hj : j < a.size), a[i] ≤ a[j]

/-- On every sorted array, the result `r` satisfies `r ≤ a.size`, and every
index `i` satisfies `i < r` exactly when `a[i] < key`. So `r` is the first index
whose element is at least `key`, or `a.size` if there is none. -/
def Correct (impl : Nat → Array Nat → Nat) : Prop :=
  ∀ key a, Sorted a →
    impl key a ≤ a.size ∧ ∀ i (hi : i < a.size), (i < impl key a ↔ a[i] < key)

end Algorithms.BinarySearch.Correctness
