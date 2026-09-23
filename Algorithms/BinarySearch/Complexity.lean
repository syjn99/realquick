import VeriQuick.Complexity
import Algorithms.BinarySearch.Impl

open VeriQuick.TimeM
open VeriQuick.Complexity
open Algorithms.BinarySearch.Impl

namespace Algorithms.BinarySearch.Complexity

def Bound (n : Nat) : Nat := Nat.log2 n + 1

/-- A single interval update takes at most sixteen instrumentation ticks. -/
theorem nextBounds_cost (a : Array Nat) (key lo hi : Nat) :
    (nextBounds_timed a key lo hi).cost ≤ 16 := by
  have hm (x y : Nat) : (midpoint_timed x y).cost = 4 := by rfl
  have hr (x : Nat) : (readAt?_timed a x).cost = 2 := by rfl
  simp only [nextBounds_timed, TimeM.cost, TimeM.snd_step, TimeM.snd_seq,
    TimeM.fst_seq, midpoint_timed_value, readAt?_timed_value]
  rw [show (midpoint_timed lo hi).2 = 4 from hm lo hi,
    show (readAt?_timed a (midpoint lo hi)).2 = 2 from hr _]
  cases h : readAt? a (midpoint lo hi) with
  | none => simp [TimeM.step, TimeM.tick, Bind.bind]
  | some v =>
    cases hlt : VeriQuick.Instrumentation.natLt v key <;>
      simp [TimeM.seq, TimeM.step, TimeM.tick, Bind.bind] <;>
      dsimp only [TimeM] <;>
      (simp [hlt]
       have hc := hm lo hi
       simp only [TimeM.cost] at hc
       omega)

/-- The instrumented loop spends at most fifty ticks per unit of fuel. -/
theorem loop_cost (a : Array Nat) (key fuel lo hi : Nat) :
    (loop_timed a key fuel lo hi).cost ≤ 50 * fuel + 2 := by
  induction fuel generalizing lo hi with
  | zero =>
    simp [loop_timed.eq_def, TimeM.cost, TimeM.step, TimeM.done,
      TimeM.tick, Bind.bind]
  | succ fuel ih =>
    rw [loop_timed.eq_def]
    simp only [TimeM.cost, TimeM.snd_step, TimeM.snd_seq]
    have h1 := nextBounds_cost a key lo hi
    have h2 := ih (lower (nextBounds a key lo hi)) (upper (nextBounds a key lo hi))
    simp only [active_timed_value, nextBounds_timed_value] at *
    simp [active_timed, lower_timed, upper_timed, TimeM.cost, TimeM.step,
      TimeM.done, TimeM.seq, TimeM.tick, Bind.bind] at h1 h2 ⊢
    simp only [lower, upper] at h2
    cases hactive : active lo hi <;> simp [hactive] at * <;> omega

/-- Uniformly in the key and array, the cost is at most 57 times the log bound. -/
theorem lowerBound_cost (key : Nat) (a : Array Nat) :
    (lowerBound_timed key a).cost ≤ 57 * Bound a.size := by
  have h := loop_cost a key (Nat.log2 a.size + 1) 0 a.size
  simp [lowerBound_timed, Bound, TimeM.cost,
    TimeM.step, TimeM.done, TimeM.seq, TimeM.tick,
    Bind.bind] at *
  omega

/-- For each key, the search cost is logarithmic in the array size. -/
theorem lowerBound_asymptotic (key : Nat) :
    Asymptotic (fun a : Array Nat => lowerBound_timed key a) (.some Bound) := by
  change ∃ c n₀ : Nat, 0 < c ∧ ∀ a : Array Nat,
    n₀ ≤ a.size → (lowerBound_timed key a).cost ≤ c * Bound a.size
  refine ⟨57, 0, by omega, ?_⟩
  intro a _
  exact lowerBound_cost key a

end Algorithms.BinarySearch.Complexity
