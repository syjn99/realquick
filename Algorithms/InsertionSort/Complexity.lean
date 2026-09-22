import Mathlib.Tactic.Ring
import RealQuick.Complexity
import Algorithms.InsertionSort.Impl

open RealQuick.TimeM
open RealQuick.Complexity
open Algorithms.InsertionSort.Impl

namespace Algorithms.InsertionSort.Complexity

/-- A quadratic bound expressed without a zero-size corner case. -/
def Bound (n : Nat) : Nat := (n + 1) ^ 2

/-- Inserting into a list takes at most five ticks per inspected element, plus
four ticks for the empty-list case. -/
theorem insert_timed_linear (x : Nat) (xs : List Nat) :
    (insert_timed x xs).cost ≤ 5 * xs.length + 4 := by
  fun_induction insert x xs with
  | case1 =>
    change 4 ≤ 4
    omega
  | case2 y ys h =>
    simp [insert_timed, RealQuick.Instrumentation.natLe, cond, h, TimeM.cost,
      TimeM.step, TimeM.tick, TimeM.done, TimeM.seq, Bind.bind]
    omega
  | case3 y ys h ih =>
    cases htimed : insert_timed x ys with
    | mk value cost =>
      simp [insert_timed, RealQuick.Instrumentation.natLe, cond, h, htimed,
        TimeM.cost, TimeM.step, TimeM.tick, TimeM.done, TimeM.seq, Bind.bind] at ih ⊢
      omega

/-- One insertion-sort step consists of sorting the tail, inserting the head,
and two outer instrumentation ticks. -/
theorem insertionSort_timed_step (x : Nat) (xs : List Nat) :
    (insertionSort_timed (x :: xs)).cost =
      (insertionSort_timed xs).cost +
      (insert_timed x (insertionSort xs)).cost + 2 := by
  cases hsort : insertionSort_timed xs with
  | mk sorted sortCost =>
    have hvalue : sorted = insertionSort xs := by
      have h := insertionSort_timed_value xs
      simpa [hsort] using h
    subst sorted
    cases hinsert : insert_timed x (insertionSort xs) with
    | mk result insertCost =>
      simp [insertionSort_timed, hsort, hinsert, TimeM.cost, TimeM.step,
        TimeM.tick, TimeM.seq, Bind.bind]

/-- The worst-case cost of insertion sort is quadratic in the input length. -/
theorem insertionSort_timed_quadratic (xs : List Nat) :
    (insertionSort_timed xs).cost ≤
      3 * xs.length * xs.length + 4 * xs.length + 3 := by
  fun_induction insertionSort xs with
  | case1 =>
    change 3 ≤ 3
    omega
  | case2 x xs ih =>
    have hstep := insertionSort_timed_step x xs
    have hinsert := insert_timed_linear x (insertionSort xs)
    rw [length_insertionSort] at hinsert
    simp only [List.length_cons]
    ring_nf at ih hinsert hstep ⊢
    omega

/-- Instrumented insertion sort is O(n²) in the input-list length. -/
def complexity : Prop :=
  Asymptotic insertionSort_timed (.some Bound)

theorem insertionSort_timed_isQuadratic : complexity := by
  refine ⟨3, 0, by decide, ?_⟩
  intro xs
  dsimp [Size.size, Bound]
  intro _
  change (insertionSort_timed xs).cost ≤ 3 * (xs.length + 1) ^ 2
  have h := insertionSort_timed_quadratic xs
  ring_nf at h ⊢
  omega

end Algorithms.InsertionSort.Complexity
