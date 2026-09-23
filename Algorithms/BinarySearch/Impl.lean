import Mathlib.Data.Nat.Log
import VeriQuick.Instrumentation
import Algorithms.BinarySearch.Correctness

open Algorithms.BinarySearch.Correctness

namespace Algorithms.BinarySearch.Impl

/-- Midpoint of the half-open interval `[lo, hi)`. -/
def midpoint (lo hi : Nat) : Nat := lo + (hi - lo) / 2

#instrument midpoint as midpoint_timed

/-- Total array lookup used by the instrumenter and the search step. -/
def readAt? (a : Array Nat) (i : Nat) : Option Nat := a[i]?

#instrument readAt? as readAt?_timed

/-- Compute the next half-open search interval. -/
def nextBounds (a : Array Nat) (key lo hi : Nat) : Nat × Nat :=
  match readAt? a (midpoint lo hi) with
  | some value =>
    if value < key then (midpoint lo hi + 1, hi)
    else (lo, midpoint lo hi)
  | none => (lo, hi)

#instrument nextBounds as nextBounds_timed

/-- First component of a pair, exposed as a helper for instrumentation. -/
def lower (bounds : Nat × Nat) : Nat := bounds.1

#instrument lower as lower_timed

/-- Second component of a pair, exposed as a helper for instrumentation. -/
def upper (bounds : Nat × Nat) : Nat := bounds.2

#instrument upper as upper_timed

/-- Whether the half-open interval `[lo, hi)` is nonempty. -/
def active (lo hi : Nat) : Bool := Nat.ble (lo + 1) hi

#instrument active as active_timed

attribute [simp] nextBounds_timed_value lower_timed_value upper_timed_value
  active_timed_value

/-- Fuel-bounded lower-bound search over a half-open interval. -/
def loop (a : Array Nat) (key : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    bif active lo hi then
      loop a key fuel
        (lower (nextBounds a key lo hi))
        (upper (nextBounds a key lo hi))
    else lo

#instrument loop as loop_timed

/-- Return the first array position whose value is at least `key`. -/
def lowerBound (key : Nat) (a : Array Nat) : Nat :=
  loop a key (Nat.log2 a.size + 1) 0 a.size

#instrument lowerBound as lowerBound_timed

-- Boundary and duplicate-key regressions; the timed value must agree too.
example : lowerBound 4 #[1, 3, 4, 4, 8] = 2 := by decide
example : lowerBound 0 #[1, 3, 4, 4, 8] = 0 := by decide
example : lowerBound 2 #[1, 3, 4, 4, 8] = 1 := by decide
example : lowerBound 9 #[1, 3, 4, 4, 8] = 5 := by decide
example : lowerBound 4 #[] = 0 := by decide
example : lowerBound 4 #[4, 4, 4] = 0 := by decide
example : (lowerBound_timed 4 #[1, 3, 4, 4, 8]).1 = 2 := by decide
example : (lowerBound_timed 9 #[1, 3, 4, 4, 8]).1 = 5 := by decide

/-- The Boolean interval test agrees with strict nonemptiness. -/
theorem active_eq_true (lo hi : Nat) : active lo hi = true ↔ lo < hi := by
  simp [active, Nat.ble_eq]
  omega

/-- A nonempty interval's midpoint lies inside that interval. -/
theorem midpoint_bounds (lo hi : Nat) (h : lo < hi) :
    lo ≤ midpoint lo hi ∧ midpoint lo hi < hi := by
  unfold midpoint
  omega

/-- The loop preserves the lower-bound partition invariants when its fuel can
cover the remaining interval. -/
theorem loop_correct (a : Array Nat) (key fuel lo hi : Nat)
    (hsorted : Sorted a)
    (hlohi : lo ≤ hi)
    (hhi : hi ≤ a.size)
    (hbound : hi - lo < 2 ^ fuel)
    (hbelow : Below a key lo)
    (habove : AtOrAbove a key hi) :
    let result := loop a key fuel lo hi
    result ≤ a.size ∧ Below a key result ∧ AtOrAbove a key result := by
  induction fuel generalizing lo hi with
  | zero =>
    have heq : lo = hi := by omega
    subst hi
    simpa [loop] using And.intro hhi (And.intro hbelow habove)
  | succ fuel ih =>
    by_cases hactive : lo < hi
    · have hactive' : active lo hi = true := (active_eq_true lo hi).2 hactive
      have hmids := midpoint_bounds lo hi hactive
      have hmidSize : midpoint lo hi < a.size := lt_of_lt_of_le hmids.2 hhi
      have hread : readAt? a (midpoint lo hi) = some a[midpoint lo hi] := by
        simp [readAt?, hmidSize]
      by_cases hvalue : a[midpoint lo hi] < key
      · have hnext : nextBounds a key lo hi = (midpoint lo hi + 1, hi) := by
          simp [nextBounds, hread, hvalue]
        rw [loop, hactive', hnext]
        simp only [lower, upper]
        apply ih (midpoint lo hi + 1) hi
        · omega
        · exact hhi
        · rw [Nat.pow_succ] at hbound
          unfold midpoint
          omega
        · intro i value hil hiread
          by_cases hilold : i < lo
          · exact hbelow i value hilold hiread
          · have himid : i ≤ midpoint lo hi := by omega
            by_cases hieq : i = midpoint lo hi
            · subst i
              have hv : a[midpoint lo hi] = value := by
                simpa [hmidSize] using hiread
              omega
            · have hltmid : i < midpoint lo hi := by omega
              have hle := hsorted i (midpoint lo hi) value a[midpoint lo hi]
                hltmid hiread (by simp [hmidSize])
              omega
        · exact habove
      · have hkey : key ≤ a[midpoint lo hi] := by omega
        have hnext : nextBounds a key lo hi = (lo, midpoint lo hi) := by
          simp [nextBounds, hread, hvalue]
        rw [loop, hactive', hnext]
        simp only [lower, upper]
        apply ih lo (midpoint lo hi)
        · exact hmids.1
        · exact le_trans (Nat.le_of_lt hmids.2) hhi
        · rw [Nat.pow_succ] at hbound
          unfold midpoint
          omega
        · exact hbelow
        · intro i value hmidi hiread
          by_cases hiold : hi ≤ i
          · exact habove i value hiold hiread
          · by_cases hieq : i = midpoint lo hi
            · subst i
              have hv : a[midpoint lo hi] = value := by
                simpa [hmidSize] using hiread
              omega
            · have hmidlt : midpoint lo hi < i := by omega
              have hle := hsorted (midpoint lo hi) i a[midpoint lo hi] value
                hmidlt (by simp [hmidSize]) hiread
              omega
    · have hactive' : active lo hi = false := by
        cases hact : active lo hi with
        | false => rfl
        | true => exact False.elim (hactive ((active_eq_true lo hi).1 hact))
      have heq : lo = hi := by omega
      subst hi
      simpa [loop, hactive'] using And.intro hhi (And.intro hbelow habove)

/-- Lower-bound binary search is correct for every sorted input array. -/
theorem lowerBound_correct : Correct lowerBound := by
  intro key a hsorted
  unfold lowerBound
  apply loop_correct a key (Nat.log2 a.size + 1) 0 a.size hsorted
  · omega
  · omega
  · simpa using Nat.lt_log2_self (n := a.size)
  · intro i value hi
    omega
  · intro i value hsize hread
    have hnot : ¬i < a.size := by omega
    simp [hnot] at hread

end Algorithms.BinarySearch.Impl
