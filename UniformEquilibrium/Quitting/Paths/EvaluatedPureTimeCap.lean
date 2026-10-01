import UniformEquilibrium.Quitting.Paths.StoppingLawEvaluatedPayoff
import MathUE.PMFProduct.Bind

/-! # Complete pure-time envelope for bounded actual clock-law evaluations

A bounded clock evaluation is an exogenous payoff convention. The response
bound is derived from the actual finite reward table, not supplied as a cap.
Private independent laws and every date/Never replacement are retained.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
private theorem evaluatedClock_abs_le
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (hzero : ∀ clock, 0 ≤ evaluation clock) (hone : ∀ clock, evaluation clock ≤ 1)
    (times : ι → Option ℕ) (who : ι) :
    |quittingPureClockEvaluatedPayoff reward evaluation times who| ≤
      quittingRewardBound reward := by
  unfold quittingPureClockEvaluatedPayoff
  cases quittingFirstStoppingOutcome times with
  | none => simpa using quittingRewardBound_nonneg reward
  | some terminal =>
      rw [abs_mul, abs_of_nonneg (hzero _)]
      exact (mul_le_mul_of_nonneg_right (hone _) (abs_nonneg _)).trans
        (by simpa using abs_reward_le_quittingRewardBound reward terminal who)

/-- Every actual evaluated replacement is the mixture of its exact pure-time replies. -/
theorem quittingBehaviorEvaluatedPayoff_update_eq_expect_pureTime
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (hzero : ∀ clock, 0 ≤ evaluation clock) (hone : ∀ clock, evaluation clock ≤ 1)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingBehaviorEvaluatedPayoff reward evaluation (Function.update profile who deviation) who =
      expect (quittingBehaviorStoppingLaw reward deviation) (fun choice =>
        quittingStoppingLawEvaluatedPayoff reward evaluation
          (Function.update (quittingBehaviorStoppingLaws reward profile) who
            (PMF.pure choice)) who) := by
  rw [quittingBehaviorEvaluatedPayoff_update]
  unfold quittingStoppingLawEvaluatedPayoff
  rw [pmfPi_update_bind, expect_bind_of_bounded (C := quittingRewardBound reward)]
  exact fun times => evaluatedClock_abs_le reward evaluation hzero hone times who

/-- The complete evaluated behavioral cap is the exact envelope of ALL dates and Never. -/
theorem quittingBehaviorEvaluatedDeviationPayoffCap_eq_pureTime
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (hzero : ∀ clock, 0 ≤ evaluation clock) (hone : ∀ clock, evaluation clock ≤ 1)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation profile who =
      sSup (Set.range fun choice : Option ℕ =>
        quittingStoppingLawEvaluatedPayoff reward evaluation
          (Function.update (quittingBehaviorStoppingLaws reward profile) who
            (PMF.pure choice)) who) := by
  classical
  let value := fun choice : Option ℕ =>
    quittingStoppingLawEvaluatedPayoff reward evaluation
      (Function.update (quittingBehaviorStoppingLaws reward profile) who (PMF.pure choice)) who
  have habs : ∀ choice, |value choice| ≤ quittingRewardBound reward := by
    intro choice
    exact abs_expect_le_of_abs_le _ _
      (fun times => evaluatedClock_abs_le reward evaluation hzero hone times who)
  have hbounded : BddAbove (Set.range value) := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro _ ⟨choice, rfl⟩
    exact (le_abs_self _).trans (habs choice)
  have hbehaviorBounded : BddAbove (Set.range fun deviation :
      (quittingGame reward).BehaviorStrategy who =>
        quittingBehaviorEvaluatedPayoff reward evaluation (Function.update profile who deviation)
          who) := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro _ ⟨deviation, rfl⟩
    exact (le_abs_self _).trans (abs_expect_le_of_abs_le _ _
      (fun times => evaluatedClock_abs_le reward evaluation hzero hone times who))
  apply le_antisymm
  · unfold quittingBehaviorEvaluatedDeviationPayoffCap
    apply csSup_le
    · exact ⟨_, ⟨quittingAlwaysContinueStrategy reward who, rfl⟩⟩
    · rintro _ ⟨deviation, rfl⟩
      change quittingBehaviorEvaluatedPayoff reward evaluation
        (Function.update profile who deviation) who ≤ sSup (Set.range value)
      rw [quittingBehaviorEvaluatedPayoff_update_eq_expect_pureTime reward evaluation hzero hone]
      change expect (quittingBehaviorStoppingLaw reward deviation) value ≤ sSup (Set.range value)
      have hle : ∀ choice, value choice ≤ sSup (Set.range value) :=
        fun choice => le_csSup hbounded ⟨choice, rfl⟩
      have hcommon : ∀ choice, |value choice| ≤
          quittingRewardBound reward + |sSup (Set.range value)| :=
        fun choice => (habs choice).trans (le_add_of_nonneg_right (abs_nonneg _))
      have hconst : ∀ _choice : Option ℕ, |sSup (Set.range value)| ≤
          quittingRewardBound reward + |sSup (Set.range value)| :=
        fun _ => le_add_of_nonneg_left (quittingRewardBound_nonneg reward)
      simpa using expect_mono_of_pointwise_bounded
        (quittingBehaviorStoppingLaw reward deviation) value
        (fun _ => sSup (Set.range value)) hle hcommon hconst
  · apply csSup_le
    · exact ⟨value none, ⟨none, rfl⟩⟩
    · rintro _ ⟨choice, rfl⟩
      unfold quittingBehaviorEvaluatedDeviationPayoffCap
      apply le_csSup hbehaviorBounded
      refine ⟨quittingStoppingLawBehaviorStrategy reward who (PMF.pure choice), ?_⟩
      change quittingBehaviorEvaluatedPayoff reward evaluation
        (Function.update profile who
          (quittingStoppingLawBehaviorStrategy reward who (PMF.pure choice))) who = value choice
      rw [quittingBehaviorEvaluatedPayoff_update,
        quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy]

end GameTheory
