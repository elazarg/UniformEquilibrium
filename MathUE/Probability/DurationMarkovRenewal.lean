/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.PivotExcursionRenewal

/-!
# Positive-duration Markov-renewal harmonic systems

This is the induction carrier left by one chronology-preserving state elimination.  Each row is
a PMF on a next state and an actual positive elapsed duration.  Backward harmonicity evaluates
the next value at that shifted time.

The ordinary homogeneous-kernel producer eliminates one pivot into this carrier and reduces
the finite state cardinality by exactly one.  Repeating the elimination requires a renewal
constructor for arbitrary positive-duration self-returns; it cannot silently reuse the
one-step geometric constructor.
-/

namespace Math.Probability

noncomputable section

open Filter

/-- A bounded backward-harmonic value process for a finite positive-duration renewal kernel. -/
structure PositiveDurationBackwardHarmonicSystem (State : Type*) [Fintype State] where
  kernel : State → PMF (State × ℕ)
  value : State → ℕ → ℝ
  duration_pos : ∀ source outcome, outcome ∈ (kernel source).support → 0 < outcome.2
  bounded : ∀ state time, value state time ∈ Set.Icc (0 : ℝ) 1
  harmonic : ∀ state time,
    expect (kernel state) (fun outcome ↦ value outcome.1 (time + outcome.2)) =
      value state time

variable {State : Type*} [Fintype State] [DecidableEq State]

theorem pivotExcursionRenewalLaw_duration_pos
    (kernel : State → PMF State) (pivot : State)
    (exit_pos : 0 < pivotExitProbability kernel pivot)
    (outcome : PivotExitState pivot × ℕ)
    (support : outcome ∈ (pivotExcursionRenewalLaw kernel pivot exit_pos).support) :
    0 < outcome.2 := by
  rw [pivotExcursionRenewalLaw] at support
  rcases (PMF.mem_support_bind_iff _ _ outcome).mp support with
    ⟨failures, _failures_support, outcome_support⟩
  rcases (PMF.mem_support_map_iff _ _ outcome).mp outcome_support with
    ⟨exit, _exit_support, outcome_eq⟩
  rw [← outcome_eq]
  omega

theorem pivotEliminatedRenewalKernel_duration_pos
    (kernel : State → PMF State) (pivot : State)
    (exit_pos : 0 < pivotExitProbability kernel pivot)
    (source outcome : PivotExitState pivot)
    (duration : ℕ)
    (support : (outcome, duration) ∈
      (pivotEliminatedRenewalKernel kernel pivot exit_pos source).support) :
    0 < duration := by
  rw [pivotEliminatedRenewalKernel] at support
  rcases (PMF.mem_support_bind_iff _ _ (outcome, duration)).mp support with
    ⟨successor, _successor_support, branch_support⟩
  by_cases successor_eq : successor = pivot
  · rw [dif_pos successor_eq] at branch_support
    rcases (PMF.mem_support_map_iff _ _ (outcome, duration)).mp branch_support with
      ⟨pivotOutcome, _pivot_support, outcome_eq⟩
    have duration_eq := congrArg Prod.snd outcome_eq
    dsimp at duration_eq
    omega
  · rw [dif_neg successor_eq] at branch_support
    have pair_eq : (outcome, duration) = (⟨successor, successor_eq⟩, 1) := by
      simpa only [PMF.support_pure, Set.mem_singleton_iff] using branch_support
    have duration_eq := congrArg Prod.snd pair_eq
    dsimp at duration_eq
    omega

/-- One ordinary homogeneous-kernel elimination produces a positive-duration renewal system
on the state type with the pivot removed. -/
def pivotEliminatedDurationSystem
    (kernel : State → PMF State) (pivot : State) (value : State → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (exit_pos : 0 < pivotExitProbability kernel pivot) :
    PositiveDurationBackwardHarmonicSystem (PivotExitState pivot) where
  kernel := pivotEliminatedRenewalKernel kernel pivot exit_pos
  value state time := value state.1 time
  duration_pos source outcome support :=
    pivotEliminatedRenewalKernel_duration_pos
      kernel pivot exit_pos source outcome.1 outcome.2 support
  bounded state time := harmonic.1 state.1 time
  harmonic state time :=
    expect_pivotEliminatedRenewalKernel_value
      kernel pivot value harmonic exit_pos state time

theorem card_pivotExitState (pivot : State) :
    Fintype.card (PivotExitState pivot) = Fintype.card State - 1 := by
  simpa only [PivotExitState, Fintype.card_unique] using
    Fintype.card_subtype_compl (fun state : State ↦ state = pivot)

namespace DurationPeelingCounterexample

/-- Two return-duration outcomes of mass `19/40` and one exit outcome of mass `1/20`. -/
def weight : Fin 3 → ℝ
  | 0 => 19 / 40
  | 1 => 19 / 40
  | 2 => 1 / 20

theorem weight_nonneg (outcome : Fin 3) : 0 ≤ weight outcome := by
  fin_cases outcome <;> norm_num [weight]

theorem weight_sum : ∑ outcome, weight outcome = 1 := by
  norm_num [weight, Fin.sum_univ_succ]

def law : PMF (Fin 3) :=
  PMF.ofFintype (fun outcome ↦ ENNReal.ofReal (weight outcome)) (by
    rw [← ENNReal.ofReal_one, ← weight_sum]
    exact (ENNReal.ofReal_sum_of_nonneg fun outcome _ ↦ weight_nonneg outcome).symm)

@[simp]
theorem law_toReal (outcome : Fin 3) : (law outcome).toReal = weight outcome := by
  rw [law, PMF.ofFintype_apply, ENNReal.toReal_ofReal (weight_nonneg outcome)]

/-- Values at the two possible return durations and at the exit duration. -/
def nextValue : Fin 3 → ℝ
  | 0 => 1 / 5
  | 1 => 4 / 5
  | 2 => 1 / 2

theorem expect_nextValue : expect law nextValue = 1 / 2 := by
  rw [expect_eq_sum]
  norm_num [law_toReal, weight, nextValue, Fin.sum_univ_succ]

theorem expect_abs_nextValue_sub_mean :
    expect law (fun outcome ↦ |nextValue outcome - 1 / 2|) = 57 / 200 := by
  rw [expect_eq_sum]
  norm_num [law_toReal, weight, nextValue, Fin.sum_univ_succ, abs_of_nonneg,
    abs_of_nonpos]

theorem bernoulliVariationPotential_one_fifth :
    bernoulliVariationPotential (1 / 5) = 4 / 5 := by
  rw [bernoulliVariationPotential]
  have hsqrt : Real.sqrt (4 / 25) = 2 / 5 := by
    rw [show (4 / 25 : ℝ) = (2 / 5) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  norm_num [hsqrt]

theorem bernoulliVariationPotential_four_fifths :
    bernoulliVariationPotential (4 / 5) = 4 / 5 := by
  rw [bernoulliVariationPotential]
  have hsqrt : Real.sqrt (4 / 25) = 2 / 5 := by
    rw [show (4 / 25 : ℝ) = (2 / 5) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  norm_num [hsqrt]

theorem bernoulliVariationPotential_one_half :
    bernoulliVariationPotential (1 / 2) = 1 := by
  rw [bernoulliVariationPotential]
  have hsqrt : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  norm_num [hsqrt]

theorem expect_returnPotential :
    expect law (fun outcome ↦
      if outcome = 2 then 0 else bernoulliVariationPotential (nextValue outcome)) =
      19 / 25 := by
  rw [expect_eq_sum]
  norm_num [law_toReal, weight, nextValue, Fin.sum_univ_succ]
  rw [bernoulliVariationPotential_one_fifth,
    bernoulliVariationPotential_four_fifths]
  simp [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide]
  norm_num

/-- A row can be harmonic at its displayed time and have positive exit mass, while the naive
partition version of one-atom Bernoulli peeling fails.  Thus repeated elimination cannot treat
all duration-labelled returns as though they were one scalar atom; it must retain their clock
dispersion or use a stronger global potential. -/
theorem partitionBernoulliPeeling_fails :
    bernoulliVariationPotential (expect law nextValue) <
      expect law (fun outcome ↦ |nextValue outcome - expect law nextValue|) +
        expect law (fun outcome ↦
          if outcome = 2 then 0 else
            bernoulliVariationPotential (nextValue outcome)) := by
  rw [expect_nextValue, expect_abs_nextValue_sub_mean, expect_returnPotential,
    bernoulliVariationPotential_one_half]
  norm_num

end DurationPeelingCounterexample

end

end Math.Probability
