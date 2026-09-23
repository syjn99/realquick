import Mathlib.Data.Nat.Log
import VeriQuick.Instrumentation
import Algorithms.BinarySearch.Correctness

open Algorithms.BinarySearch.Correctness

namespace Algorithms.BinarySearch.Impl

/-!
Lower-bound binary search over the half-open interval `[lo, hi)`.

The small helpers below exist so that `#instrument` can prove value
preservation: the array read goes through `readAt?`, the interval test through
`active`, and the pair projections through `lower` and `upper`. `loop` calls
`nextBounds` twice because the instrumenter cannot yet handle a `let` there.
`loop` branches with `match` rather than `bif`: the instrumented `bif` charges
both branches, so the finished loop would still pay for a recursive call.
-/

/-- Midpoint of the half-open interval `[lo, hi)`. -/
def midpoint (lo hi : Nat) : Nat := lo + (hi - lo) / 2

#instrument midpoint as midpoint_timed

/-- Total array lookup. -/
def readAt? (a : Array Nat) (i : Nat) : Option Nat := a[i]?

#instrument readAt? as readAt?_timed

/-- One search step: compare the midpoint element with `key` and keep the half
that still contains the answer. The `none` case does not occur when
`hi ≤ a.size`. -/
def nextBounds (a : Array Nat) (key lo hi : Nat) : Nat × Nat :=
  match readAt? a (midpoint lo hi) with
  | some value =>
    if value < key then (midpoint lo hi + 1, hi)
    else (lo, midpoint lo hi)
  | none => (lo, hi)

#instrument nextBounds as nextBounds_timed

/-- First component of a pair. -/
def lower (bounds : Nat × Nat) : Nat := bounds.1

#instrument lower as lower_timed

/-- Second component of a pair. -/
def upper (bounds : Nat × Nat) : Nat := bounds.2

#instrument upper as upper_timed

/-- Whether the half-open interval `[lo, hi)` is nonempty. -/
def active (lo hi : Nat) : Bool := Nat.ble (lo + 1) hi

#instrument active as active_timed

attribute [simp] nextBounds_timed_value lower_timed_value upper_timed_value
  active_timed_value

/-- Fuel-bounded lower-bound search over `[lo, hi)`. -/
def loop (a : Array Nat) (key : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    match active lo hi with
    | true =>
      loop a key fuel
        (lower (nextBounds a key lo hi))
        (upper (nextBounds a key lo hi))
    | false => lo

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

/-- `lo ≤ hi ≤ a.size`, every element before `lo` is below `key`, and every
element from `hi` on is at least `key`. -/
def Inv (a : Array Nat) (key lo hi : Nat) : Prop :=
  lo ≤ hi ∧ hi ≤ a.size ∧
    (∀ i (h : i < a.size), i < lo → a[i] < key) ∧
    (∀ i (h : i < a.size), hi ≤ i → key ≤ a[i])

theorem sorted_le {a : Array Nat} (hs : Sorted a) {i j : Nat} (hij : i ≤ j)
    (hj : j < a.size) : a[i] ≤ a[j] := by
  rcases Nat.lt_or_eq_of_le hij with h | rfl
  · exact hs i j h hj
  · exact Nat.le_refl _

theorem active_eq_true (lo hi : Nat) : active lo hi = true ↔ lo < hi := by
  simp only [active, Nat.ble_eq]
  omega

theorem nextBounds_eq (a : Array Nat) (key lo hi : Nat) (h : midpoint lo hi < a.size) :
    nextBounds a key lo hi =
      if a[midpoint lo hi] < key then (midpoint lo hi + 1, hi)
      else (lo, midpoint lo hi) := by
  simp only [nextBounds, readAt?, Array.getElem?_eq_getElem h]

/-- A step on a nonempty interval preserves `Inv`. -/
theorem nextBounds_inv {a : Array Nat} {key lo hi : Nat} (hs : Sorted a)
    (h : Inv a key lo hi) (hlt : lo < hi) :
    Inv a key (lower (nextBounds a key lo hi)) (upper (nextBounds a key lo hi)) := by
  obtain ⟨_, hhi, hbelow, habove⟩ := h
  have hm : midpoint lo hi < a.size := by unfold midpoint; omega
  rw [nextBounds_eq a key lo hi hm]
  split <;> simp only [lower, upper]
  · refine ⟨by unfold midpoint; omega, hhi, fun i hi hlt' => ?_, habove⟩
    exact Nat.lt_of_le_of_lt (sorted_le hs (by omega) hm) ‹_›
  · refine ⟨by unfold midpoint; omega, by omega, hbelow, fun i hi hle => ?_⟩
    exact Nat.le_trans (by omega) (sorted_le hs hle hi)

/-- A step on a nonempty interval at least halves its length. -/
theorem nextBounds_halves (a : Array Nat) (key lo hi : Nat) (hlt : lo < hi)
    (hhi : hi ≤ a.size) :
    2 * (upper (nextBounds a key lo hi) - lower (nextBounds a key lo hi)) ≤ hi - lo := by
  have hm : midpoint lo hi < a.size := by unfold midpoint; omega
  rw [nextBounds_eq a key lo hi hm]
  split <;> simp only [lower, upper, midpoint] <;> omega

/-- With enough fuel, `loop` returns a point `r` with `Inv a key r r`. -/
theorem loop_inv (a : Array Nat) (key fuel lo hi : Nat) (hs : Sorted a)
    (h : Inv a key lo hi) (hfuel : hi - lo < 2 ^ fuel) :
    Inv a key (loop a key fuel lo hi) (loop a key fuel lo hi) := by
  fun_induction loop a key fuel lo hi with
  | case1 lo hi =>
    have heq : hi = lo := by have := h.1; simp only [Nat.pow_zero] at hfuel; omega
    subst heq
    exact h
  | case2 fuel lo hi hact ih =>
    have hlt := (active_eq_true lo hi).1 hact
    apply ih (nextBounds_inv hs h hlt)
    have := nextBounds_halves a key lo hi hlt h.2.1
    rw [Nat.pow_succ] at hfuel
    omega
  | case3 fuel lo hi hact =>
    have hle : ¬lo < hi := fun hlt => by
      rw [(active_eq_true lo hi).2 hlt] at hact
      contradiction
    have heq : hi = lo := by have := h.1; omega
    subst heq
    exact h

/-- Lower-bound binary search is correct for every sorted input array. -/
theorem lowerBound_correct : Correct lowerBound := by
  intro key a hs
  have hinit : Inv a key 0 a.size :=
    ⟨Nat.zero_le _, Nat.le_refl _, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ hi hle => absurd hi (Nat.not_lt_of_le hle)⟩
  obtain ⟨_, hsize, hbelow, habove⟩ :=
    loop_inv a key (Nat.log2 a.size + 1) 0 a.size hs hinit
      (by simpa only [Nat.sub_zero] using Nat.lt_log2_self (n := a.size))
  refine ⟨hsize, fun i hi => ⟨hbelow i hi, fun hv => ?_⟩⟩
  exact Nat.lt_of_not_le fun hle => Nat.not_lt_of_le (habove i hi hle) hv

end Algorithms.BinarySearch.Impl
