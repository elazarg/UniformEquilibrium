import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPointwiseDomination
import UniformEquilibrium.Quitting.Paths.StoppingLawReconstruction
import MathUE.ProbabilityMassFunction.StoppingLawLateIndicators

/-!
# Private-law compiler for capped clocks

The capped law samples the prescribed clock and a fresh independent outsider
clock, then takes their literal minimum.  Reconstruction makes the resulting
law an actual unilateral behavioral strategy; no finite-support or
cap-attainment hypothesis is used.
-/

noncomputable section

namespace GameTheory

open Math.Probability

/-- Independent min-pushforward of two complete finite-or-Never clock laws. -/
def cappedClockStoppingLaw (source deadline : PMF (Option ℕ)) :
    PMF (Option ℕ) :=
  source.bind fun sourceClock =>
    deadline.map fun deadlineClock =>
      cappedStoppingClock sourceClock deadlineClock

@[simp] theorem cappedClockStoppingLaw_pure
    (source deadline : Option ℕ) :
    cappedClockStoppingLaw (PMF.pure source) (PMF.pure deadline) =
      PMF.pure (cappedStoppingClock source deadline) := by
  simp [cappedClockStoppingLaw, PMF.pure_map]

/-- The min-pushforward is an actual unrestricted behavioral replacement and
its induced stopping law is exactly the compiled law. -/
theorem quittingBehaviorStoppingLaw_cappedClockStrategy
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (who : ι) (source deadline : PMF (Option ℕ)) :
    quittingBehaviorStoppingLaw reward
        (quittingStoppingLawBehaviorStrategy reward who
          (cappedClockStoppingLaw source deadline)) =
      cappedClockStoppingLaw source deadline := by
  exact quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy
    reward who (cappedClockStoppingLaw source deadline)

/-- A pure outsider deadline gives the pushforward by the literal deterministic
cap operation appearing in the pointwise theorem. -/
theorem cappedClockStoppingLaw_pure_deadline
    (source : PMF (Option ℕ)) (deadline : Option ℕ) :
    cappedClockStoppingLaw source (PMF.pure deadline) =
      source.map fun sourceClock => cappedStoppingClock sourceClock deadline := by
  unfold cappedClockStoppingLaw
  simp_rw [PMF.pure_map]
  exact PMF.bind_pure_comp _ source

/-- Expectation under the compiled law is iterated expectation over the two
independent private clocks.  This is the integration interface for the
pointwise domination theorem. -/
theorem expect_cappedClockStoppingLaw_of_bounded
    (source deadline : PMF (Option ℕ)) (value : Option ℕ → ℝ)
    {bound : ℝ} (hvalue : ∀ clock, |value clock| ≤ bound) :
    expect (cappedClockStoppingLaw source deadline) value =
      expect source fun sourceClock =>
        expect deadline fun deadlineClock =>
          value (cappedStoppingClock sourceClock deadlineClock) := by
  unfold cappedClockStoppingLaw
  rw [expect_bind_of_bounded source _ value hvalue]
  apply congrArg (expect source)
  funext sourceClock
  exact Math.ProbabilityMassFunction.expect_pushforward_of_bounded
    deadline (fun deadlineClock => cappedStoppingClock sourceClock deadlineClock)
      value hvalue

private theorem tailIndicator_cappedStoppingClock
    (cutoff : ℕ) (source deadline : Option ℕ) :
    stoppingLawTailIndicator cutoff (cappedStoppingClock source deadline) =
      stoppingLawTailIndicator cutoff source *
        stoppingLawTailIndicator cutoff deadline := by
  have hindicator (clock : Option ℕ) :
      stoppingLawTailIndicator cutoff clock =
        if (cutoff : WithTop ℕ) ≤ quittingStoppingTimeValue clock then 1 else 0 := by
    cases clock with
    | none => simp [stoppingLawTailIndicator, quittingStoppingTimeValue]
    | some time =>
        simp [stoppingLawTailIndicator, quittingStoppingTimeValue,
          Finset.mem_image]
        by_cases h : time < cutoff
        · simp [h, Nat.not_le_of_gt h]
        · simp [h, Nat.le_of_not_gt h]
  have hmin : quittingStoppingTimeValue (cappedStoppingClock source deadline) =
      min (quittingStoppingTimeValue source)
        (quittingStoppingTimeValue deadline) := by
    unfold cappedStoppingClock
    split_ifs with h
    · exact (min_eq_left h).symm
    · exact (min_eq_right (le_of_not_ge h)).symm
  rw [hindicator, hindicator, hindicator, hmin]
  simp only [le_min_iff]
  by_cases hsource : (cutoff : WithTop ℕ) ≤ quittingStoppingTimeValue source <;>
    by_cases hdeadline : (cutoff : WithTop ℕ) ≤
      quittingStoppingTimeValue deadline <;> simp [hsource, hdeadline]

/-- Inclusive survival of the independent minimum is the product of the two
inclusive survival probabilities. -/
theorem cappedClockStoppingLaw_survival
    (source deadline : PMF (Option ℕ)) (cutoff : ℕ) :
    DiscreteHazard.StoppingLaw.survival
        (cappedClockStoppingLaw source deadline) cutoff =
      DiscreteHazard.StoppingLaw.survival source cutoff *
        DiscreteHazard.StoppingLaw.survival deadline cutoff := by
  rw [← expect_stoppingLawTailIndicator,
    expect_cappedClockStoppingLaw_of_bounded source deadline
      (stoppingLawTailIndicator cutoff)
      (abs_stoppingLawTailIndicator_le_one cutoff)]
  simp_rw [tailIndicator_cappedStoppingClock, expect_const_mul]
  simp_rw [mul_comm]
  rw [expect_const_mul, expect_stoppingLawTailIndicator,
    expect_stoppingLawTailIndicator]
  ring

end GameTheory
