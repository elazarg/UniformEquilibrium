import MathUE.Probability.OverlappingFirstStopping
import MathUE.Probability.DiscreteHazardConditionalMixture

/-! # Exact infinite first-stopping recurrences after a hazard shift -/

noncomputable section

namespace Math.Probability.DiscreteHazard.ScalarHazard

open StoppingLaw

/-- The first overlapping event in the independent residual stopping laws. -/
def equalFirstSecondBeforeThirdTailMass
    (first second third : ScalarHazard) (start : ℕ) : ℝ :=
  equalFirstSecondBeforeThirdMass (first.shift start).stoppingLaw
    (second.shift start).stoppingLaw (third.shift start).stoppingLaw

/-- The symmetric overlapping event in the independent residual stopping laws. -/
def equalFirstThirdBeforeSecondTailMass
    (first second third : ScalarHazard) (start : ℕ) : ℝ :=
  equalFirstThirdBeforeSecondMass (first.shift start).stoppingLaw
    (second.shift start).stoppingLaw (third.shift start).stoppingLaw

private def overlapTerm (first second third : ScalarHazard) (start time : ℕ) : ℝ :=
  first.survival start time * second.survival start time *
    third.survival start time * first.stop (start + time) *
      second.stop (start + time) * (1 - third.stop (start + time))

private theorem shifted_mass_term_eq
    (first second third : ScalarHazard) (start time : ℕ) :
    finiteMass (first.shift start).stoppingLaw time *
        finiteMass (second.shift start).stoppingLaw time *
        StoppingLaw.survival (third.shift start).stoppingLaw (time + 1) =
      overlapTerm first second third start time := by
  simp only [finiteMass, stoppingLaw_some_toReal, stopMass,
    StoppingLaw.survival_stoppingLaw, shift_survival_zero, shift_stop]
  rw [survival_succ]
  unfold overlapTerm
  ring

private theorem summable_overlapTerm
    (first second third : ScalarHazard) (start : ℕ) :
    Summable (overlapTerm first second third start) := by
  have h := summable_equalFirstSecondBeforeThirdMass_terms
    (first.shift start).stoppingLaw (second.shift start).stoppingLaw
      (third.shift start).stoppingLaw
  simpa only [shifted_mass_term_eq] using h

private theorem equalFirstSecondBeforeThirdTailMass_eq_tsum
    (first second third : ScalarHazard) (start : ℕ) :
    equalFirstSecondBeforeThirdTailMass first second third start =
      ∑' time, overlapTerm first second third start time := by
  unfold equalFirstSecondBeforeThirdTailMass equalFirstSecondBeforeThirdMass
  exact tsum_congr (shifted_mass_term_eq first second third start)

/-- Infinite overlapping-event mass splits into its first row and the exact
joint-survival multiple of the residual event. Zero continuation is included. -/
theorem equalFirstSecondBeforeThirdTailMass_succ
    (first second third : ScalarHazard) (start : ℕ) :
    equalFirstSecondBeforeThirdTailMass first second third start =
      first.stop start * second.stop start * (1 - third.stop start) +
        (1 - first.stop start) * (1 - second.stop start) *
          (1 - third.stop start) *
            equalFirstSecondBeforeThirdTailMass first second third (start + 1) := by
  rw [equalFirstSecondBeforeThirdTailMass_eq_tsum,
    (summable_overlapTerm first second third start).tsum_eq_zero_add,
    equalFirstSecondBeforeThirdTailMass_eq_tsum, ← tsum_mul_left]
  have hzero : overlapTerm first second third start 0 =
      first.stop start * second.stop start * (1 - third.stop start) := by
    simp [overlapTerm, survival_zero]
  rw [hzero]
  congr 1
  apply tsum_congr
  intro time
  unfold overlapTerm
  rw [survival_succ_left, survival_succ_left, survival_succ_left]
  simp only [Nat.add_comm, Nat.add_left_comm]
  ring

theorem equalFirstThirdBeforeSecondTailMass_eq_swap
    (first second third : ScalarHazard) (start : ℕ) :
    equalFirstThirdBeforeSecondTailMass first second third start =
      equalFirstSecondBeforeThirdTailMass first third second start := rfl

/-- The symmetric exact infinite first-row recurrence. -/
theorem equalFirstThirdBeforeSecondTailMass_succ
    (first second third : ScalarHazard) (start : ℕ) :
    equalFirstThirdBeforeSecondTailMass first second third start =
      first.stop start * third.stop start * (1 - second.stop start) +
        (1 - first.stop start) * (1 - second.stop start) *
          (1 - third.stop start) *
            equalFirstThirdBeforeSecondTailMass first second third (start + 1) := by
  rw [equalFirstThirdBeforeSecondTailMass_eq_swap,
    equalFirstSecondBeforeThirdTailMass_succ,
    equalFirstThirdBeforeSecondTailMass_eq_swap]
  ring

theorem twoOverlappingFirstStoppingTailMasses_sqrt_sum_le_one
    (first second third : ScalarHazard) (start : ℕ) :
    Real.sqrt (equalFirstSecondBeforeThirdTailMass first second third start) +
      Real.sqrt (equalFirstThirdBeforeSecondTailMass first second third start) ≤ 1 :=
  twoOverlappingFirstStoppingMasses_sqrt_sum_le_one
    (first.shift start).stoppingLaw (second.shift start).stoppingLaw
    (third.shift start).stoppingLaw

end Math.Probability.DiscreteHazard.ScalarHazard
