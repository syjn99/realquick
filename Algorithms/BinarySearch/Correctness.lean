namespace Algorithms.BinarySearch.Correctness

/-- An array is sorted when every successfully read earlier element is at most
every successfully read later element. -/
def Sorted (a : Array Nat) : Prop :=
  ∀ (i j vi vj : Nat),
    i < j → a[i]? = some vi → a[j]? = some vj → vi ≤ vj

/-- Every present value before `bound` is strictly below `key`. -/
def Below (a : Array Nat) (key bound : Nat) : Prop :=
  ∀ (i value : Nat), i < bound → a[i]? = some value → value < key

/-- Every present value from `bound` onward is at least `key`. -/
def AtOrAbove (a : Array Nat) (key bound : Nat) : Prop :=
  ∀ (i value : Nat), bound ≤ i → a[i]? = some value → key ≤ value

/-- A lower-bound search returns the first position whose value is at least the
key, or the array size when every value is smaller. -/
def Correct (impl : Nat → Array Nat → Nat) : Prop :=
  ∀ key a, Sorted a →
    let result := impl key a
    result ≤ a.size ∧
      Below a key result ∧ AtOrAbove a key result

end Algorithms.BinarySearch.Correctness
