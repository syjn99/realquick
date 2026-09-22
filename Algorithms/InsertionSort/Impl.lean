import RealQuick.Instrumentation
import Algorithms.InsertionSort.Correctness

open Algorithms.InsertionSort.Correctness

namespace Algorithms.InsertionSort.Impl

/-- Insert `x` into its sorted position in a list. -/
def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if x ≤ y then x :: y :: ys
    else y :: insert x ys

/-- Sort a list by repeatedly inserting each head into the sorted tail. -/
def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (insertionSort xs)

/-- Insertion preserves exactly the inserted value and the original elements. -/
theorem insert_perm (x : Nat) (xs : List Nat) :
    (insert x xs).Perm (x :: xs) := by
  fun_induction insert x xs with
  | case1 => rfl
  | case2 => rfl
  | case3 y ys h ih =>
    exact (ih.cons y).trans (List.Perm.swap y x ys).symm

/-- Inserting into a sorted list preserves sortedness. -/
theorem insert_sorted (x : Nat) (xs : List Nat) (hxs : Sorted xs) :
    Sorted (insert x xs) := by
  induction xs with
  | nil => simp [insert, Sorted]
  | cons y ys ih =>
    obtain ⟨hy, hys⟩ := List.pairwise_cons.mp hxs
    by_cases hxy : x ≤ y
    · rw [insert]
      simp only [hxy, ↓reduceIte]
      apply List.pairwise_cons.mpr
      constructor
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hxy
        · exact Nat.le_trans hxy (hy z hz)
      · exact hxs
    · rw [insert]
      simp only [hxy, ↓reduceIte]
      apply List.pairwise_cons.mpr
      constructor
      · intro z hz
        have hz' := (insert_perm x ys).mem_iff.mp hz
        rcases List.mem_cons.mp hz' with rfl | hz'
        · omega
        · exact hy z hz'
      · exact ih hys

/-- Insertion sort always returns a sorted list. -/
theorem insertionSort_sorted (xs : List Nat) : Sorted (insertionSort xs) := by
  induction xs with
  | nil => simp [insertionSort, Sorted]
  | cons x xs ih =>
    exact insert_sorted x (insertionSort xs) ih

/-- Insertion sort preserves the input multiset. -/
theorem insertionSort_perm (xs : List Nat) : (insertionSort xs).Perm xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    exact (insert_perm x (insertionSort xs)).trans (ih.cons x)

/-- Insertion sort preserves the input length. -/
theorem length_insertionSort (xs : List Nat) :
    (insertionSort xs).length = xs.length :=
  (insertionSort_perm xs).length_eq

/-- Insertion sort is correct: its output is sorted and a permutation of its
input. -/
theorem insertionSort_correct : Correct insertionSort := by
  intro xs
  exact ⟨insertionSort_sorted xs, insertionSort_perm xs⟩

#instrument insert as insert_timed
#instrument insertionSort as insertionSort_timed

end Algorithms.InsertionSort.Impl
