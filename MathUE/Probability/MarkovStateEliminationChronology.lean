/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.MarkovStateElimination

/-!
# Chronology obstruction for ordinary Markov state elimination

The static Schur complement in `MarkovStateElimination` does not preserve a time-dependent
backward-harmonic orbit on the same one-step clock.  A transition collapsed through the pivot
uses two or more original time steps, while the ordinary reduced kernel advances the orbit by
only one time step.

The four-state example below is exact and unit-interval valued.  The pivot lies between a
transient source and a deterministic period-two closed class.  Ordinary Schur elimination
turns the two-step path into a one-step path and reverses its phase.  In particular, the
time-indexed analogue of the static nonnegative triangle excess can be negative.
-/

namespace Math.Probability

noncomputable section

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- The part of a matrix row which exits the pivot, evaluated against a time slice. -/
def pivotExitValue
    (matrix : State → State → ℝ) (value : State → ℕ → ℝ)
    (pivot : State) (time : ℕ) : ℝ :=
  ∑ target ∈ Finset.univ.erase pivot, matrix pivot target * value target time

/-- One backward-harmonic step at the pivot, split into the self-loop and exits. -/
theorem backwardHarmonic_pivot_eq_self_add_exit
    (matrix : State → State → ℝ) (value : State → ℕ → ℝ) (pivot : State)
    (harmonic : ∀ state time,
      value state time = ∑ target, matrix state target * value target (time + 1))
    (time : ℕ) :
    value pivot time = matrix pivot pivot * value pivot (time + 1) +
      pivotExitValue matrix value pivot (time + 1) := by
  rw [harmonic pivot time, ← Finset.sum_erase_add Finset.univ
    (fun target ↦ matrix pivot target * value target (time + 1))
    (Finset.mem_univ pivot)]
  simp only [pivotExitValue]
  ring

/-- Exact finite duration-labelled unrolling of a pivot excursion.  Unlike the ordinary Schur
complement, the exit after `step` self-loops is evaluated at the actual later time. -/
theorem backwardHarmonic_pivot_unroll
    (matrix : State → State → ℝ) (value : State → ℕ → ℝ) (pivot : State)
    (harmonic : ∀ state time,
      value state time = ∑ target, matrix state target * value target (time + 1))
    (time rounds : ℕ) :
    value pivot time =
      (matrix pivot pivot) ^ rounds * value pivot (time + rounds) +
        ∑ step ∈ Finset.range rounds,
          (matrix pivot pivot) ^ step *
            pivotExitValue matrix value pivot (time + step + 1) := by
  induction rounds with
  | zero => simp
  | succ rounds ih =>
      rw [ih, Finset.sum_range_succ,
        backwardHarmonic_pivot_eq_self_add_exit matrix value pivot harmonic
          (time + rounds)]
      rw [pow_succ]
      ring_nf

/-- Exact finite chronology-preserving elimination formula at a predecessor of the pivot.
The direct exits take one original step; a pivot exit after `step` self-loops takes
`step + 2` original steps. -/
theorem backwardHarmonic_source_unroll_pivot
    (matrix : State → State → ℝ) (value : State → ℕ → ℝ)
    (pivot source : State)
    (harmonic : ∀ state time,
      value state time = ∑ target, matrix state target * value target (time + 1))
    (time rounds : ℕ) :
    value source time =
      (∑ target ∈ Finset.univ.erase pivot,
        matrix source target * value target (time + 1)) +
      matrix source pivot *
        ((matrix pivot pivot) ^ rounds * value pivot (time + rounds + 1) +
          ∑ step ∈ Finset.range rounds,
            (matrix pivot pivot) ^ step *
              pivotExitValue matrix value pivot (time + step + 2)) := by
  rw [harmonic source time, ← Finset.sum_erase_add Finset.univ
    (fun target ↦ matrix source target * value target (time + 1))
    (Finset.mem_univ pivot)]
  rw [backwardHarmonic_pivot_unroll matrix value pivot harmonic (time + 1) rounds]
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

namespace SchurChronologyCounterexample

/-- The alternating zero-one boundary datum. -/
def alternatingValue (time : ℕ) : ℝ := if Even time then 0 else 1

theorem alternatingValue_succ (time : ℕ) :
    alternatingValue (time + 1) = 1 - alternatingValue time := by
  unfold alternatingValue
  by_cases even : Even time
  · rw [if_pos even, if_neg]
    · norm_num
    · exact Nat.not_even_iff_odd.mpr even.add_one
  · rw [if_neg even, if_pos]
    · norm_num
    · exact Nat.even_add_one.mpr even

theorem alternatingValue_succ_succ (time : ℕ) :
    alternatingValue (time + 2) = alternatingValue time := by
  rw [show time + 2 = (time + 1) + 1 by omega, alternatingValue_succ,
    alternatingValue_succ]
  ring

theorem alternatingValue_mem_Icc (time : ℕ) :
    alternatingValue time ∈ Set.Icc (0 : ℝ) 1 := by
  unfold alternatingValue
  split_ifs <;> norm_num

/-- State `0` is the pivot, state `1` is its transient predecessor, and `2,3` form the
period-two closed class. -/
def nextState : Fin 4 → Fin 4
  | 0 => 2
  | 1 => 0
  | 2 => 3
  | 3 => 2

/-- Deterministic transition matrix of the chronology counterexample. -/
def matrix (source target : Fin 4) : ℝ :=
  if target = nextState source then 1 else 0

theorem matrix_nonneg (source target : Fin 4) :
    0 ≤ matrix source target := by
  unfold matrix
  split_ifs <;> norm_num

theorem matrix_row_sum (source : Fin 4) :
    ∑ target, matrix source target = 1 := by
  simp [matrix]

/-- A bounded backward-harmonic orbit whose recurrent boundary alternates with period two. -/
def value (state : Fin 4) (time : ℕ) : ℝ :=
  match state with
  | 0 => 1 - alternatingValue time
  | 1 => alternatingValue time
  | 2 => alternatingValue time
  | 3 => 1 - alternatingValue time

theorem value_mem_Icc (state : Fin 4) (time : ℕ) :
    value state time ∈ Set.Icc (0 : ℝ) 1 := by
  rcases alternatingValue_mem_Icc time with ⟨halt0, halt1⟩
  fin_cases state <;> simp only [value] <;> constructor <;> linarith

theorem backwardHarmonic (state : Fin 4) (time : ℕ) :
    value state time = ∑ successor, matrix state successor * value successor (time + 1) := by
  have hsucc := alternatingValue_succ time
  fin_cases state <;> simp [matrix, nextState, value] <;> linarith

theorem pivot_exit_pos : 0 < 1 - matrix 0 0 := by
  simp [matrix, nextState, show (0 : Fin 4) ≠ 2 by decide]

/-- Static Schur elimination advances the target by one displayed time step, although the
collapsed path used two original steps.  The restricted orbit is therefore not harmonic for
the ordinary reduced kernel. -/
theorem not_schurBackwardHarmonic_sameClock :
    value 1 0 ≠
      ∑ target ∈ Finset.univ.erase (0 : Fin 4),
        schurWeight matrix 0 1 target * value target 1 := by
  have herase : Finset.univ.erase (0 : Fin 4) = {1, 2, 3} := by decide
  rw [herase]
  simp [value, alternatingValue, schurWeight, matrix, nextState,
    Finset.sum_insert, show (0 : Fin 4) ≠ 2 by decide]

/-- The naive time-indexed triangle excess is negative: both original increments vanish,
while the one-clock Schur edge has variation one. -/
theorem chronologicalTriangleExcess_eq_neg_one :
    |value 0 1 - value 1 0| + |value 2 2 - value 0 1| -
        |value 2 1 - value 1 0| = (-1 : ℝ) := by
  norm_num [value, alternatingValue]

end SchurChronologyCounterexample

end

end Math.Probability
