import MathUE.PowerCutoffLogBound
import UniformEquilibrium.Quitting.Stationary.FiniteCensor

/-! # Logarithmic date cutoffs and the zero-survival one-date boundary

These consumers retain the actual stationary censor family. The logarithmic
index delegates the scalar power-cutoff theorem; zero deleted-opponent
survival already gives exact terminal semantics after one retained date.
No uniform constant across stationary roots approaching unit survival is asserted.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The sharp stationary censor has an explicit logarithmic date cutoff.
The root and its logarithmic scale are fixed before the accuracy. -/
theorem stationaryFiniteCensor_logCutoff_bounds
    (root : ι → PMF Bool) {M accuracy : ℝ}
    (hcontracts : ∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1)
    (haccuracy : 0 < accuracy) (hsmall : accuracy ≤ 3 * M) :
    let deadline := Math.powerLogCutoff
      (quittingStationaryDeletedSurvivalMax root) (accuracy / (3 * M))
    0 < deadline ∧
      3 * M * quittingStationaryDeletedSurvivalMax root ^ deadline ≤ accuracy ∧
      M * quittingStationaryDeletedSurvivalMax root ^ deadline ≤ accuracy / 3 ∧
      (deadline : ℝ) ≤ 1 +
        Math.survivalLogScale (quittingStationaryDeletedSurvivalMax root) *
          Real.log (3 * M / accuracy) := by
  have hM : 0 < M := by linarith
  have hfactor : 0 < 3 * M := by positivity
  have htolerance : 0 < accuracy / (3 * M) := div_pos haccuracy hfactor
  have htolerance1 : accuracy / (3 * M) ≤ 1 := (div_le_one hfactor).mpr hsmall
  have hspec := Math.powerLogCutoff_spec_and_bound
    (quittingStationaryDeletedSurvivalMax_nonneg root)
    (quittingStationaryDeletedSurvivalMax_lt_one root hcontracts) htolerance htolerance1
  have hscaled := mul_le_mul_of_nonneg_left hspec.2.1 hfactor.le
  have hcancel : 3 * M * (accuracy / (3 * M)) = accuracy :=
    mul_div_cancel₀ accuracy hfactor.ne'
  rw [hcancel] at hscaled
  refine ⟨hspec.1, hscaled, ?_, ?_⟩
  · nlinarith [hscaled]
  · simpa only [one_div_div] using hspec.2.2

/-- The same finite laws attain the requested terminal accuracy with the
displayed logarithmic date count and all signed finite-horizon bounds. -/
theorem exists_stationaryFiniteCensorTimingProfile_logCutoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {M accuracy : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root))
    (hcontracts : ∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1)
    (haccuracy : 0 < accuracy) (hsmall : accuracy ≤ 3 * M) :
    let deadline := Math.powerLogCutoff
      (quittingStationaryDeletedSurvivalMax root) (accuracy / (3 * M))
    0 < deadline ∧
      (deadline : ℝ) ≤ 1 +
        Math.survivalLogScale (quittingStationaryDeletedSurvivalMax root) *
          Real.log (3 * M / accuracy) ∧
      ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
        (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
          censorLateFiniteStoppingLaw
            (quittingBehaviorStoppingLaw reward (quittingStationaryProfile reward root who))
            (deadline - 1)) ∧
        quittingTerminalSemanticPair reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) =
          quittingTerminalSemanticPair reward
            (quittingStationaryFiniteCensorProfile reward root deadline) ∧
        (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) ∧
        (∀ who, |quittingTerminalPayoff reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who -
          quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
            accuracy / 3) ∧
        ∀ horizon, 0 < horizon →
          (quittingGame reward).IsεHorizonNash none horizon
            (accuracy + 2 * M * (deadline + 1) / horizon)
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) who -
            quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
              accuracy / 3 + M * (deadline + 1) / horizon := by
  let deadline := Math.powerLogCutoff
    (quittingStationaryDeletedSurvivalMax root) (accuracy / (3 * M))
  obtain ⟨hpositive, hregret, hdelivery, hlength⟩ :=
    stationaryFiniteCensor_logCutoff_bounds root hcontracts haccuracy hsmall
  obtain ⟨_, mixed, hlaws, hpair, _, _, _, hterminal, htarget, hhorizon⟩ :=
    exists_stationaryFiniteCensorTimingProfile reward root deadline hpositive
      hreward hnash hcontracts
  refine ⟨hpositive, hlength, mixed, hlaws, hpair, ?_, ?_, ?_⟩
  · intro who deviation
    exact (hterminal who deviation).trans (_root_.add_le_add le_rfl hregret)
  · intro who
    exact (htarget who).trans hdelivery
  · intro horizon hpositive
    obtain ⟨hnashH, htargetH⟩ := hhorizon horizon hpositive
    constructor
    · intro who deviation
      exact (hnashH who deviation).trans
        (_root_.add_le_add le_rfl (_root_.add_le_add hregret le_rfl))
    · intro who
      exact (htargetH who).trans (_root_.add_le_add hdelivery le_rfl)

/-- Zero survival selects exactly one date even in the logarithmic comparison API. -/
theorem stationaryFiniteCensor_logCutoff_eq_one_of_zero
    (root : ι → PMF Bool) (hzero : quittingStationaryDeletedSurvivalMax root = 0)
    (tolerance : ℝ) :
    Math.powerLogCutoff (quittingStationaryDeletedSurvivalMax root) tolerance = 1 := by
  rw [hzero, Math.powerLogCutoff_zero]

/-- When every deleted-opponent clock absorbs in one date, censoring the
same root after one date preserves prescribed payoff and full cap exactly. -/
theorem exists_stationaryFiniteCensor_oneDate_exact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root))
    (hzero : quittingStationaryDeletedSurvivalMax root = 0) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction 1),
      (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        censorLateFiniteStoppingLaw
          (quittingBehaviorStoppingLaw reward (quittingStationaryProfile reward root who)) 0) ∧
      quittingTerminalSemanticPair reward
          (quittingFiniteDeadlineTimingProfile reward 1 mixed) =
        quittingTerminalSemanticPair reward
          (quittingStationaryFiniteCensorProfile reward root 1) ∧
      (∀ who, quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward 1 mixed) who =
        quittingTerminalPayoff reward (quittingStationaryProfile reward root) who) ∧
      (∀ who, quittingContinuationBestResponseValue reward
          (quittingFiniteDeadlineTimingProfile reward 1 mixed) who =
        quittingTerminalPayoff reward (quittingStationaryProfile reward root) who) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingFiniteDeadlineTimingProfile reward 1 mixed) := by
  have hcontracts (who : ι) :
      quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    have hle := quittingStationaryFixedOpponentsContinueMass_le_max root who
    rw [hzero] at hle
    linarith
  obtain ⟨_, mixed, hlaws, hpair, _, _, _, hterminal, hdelivery, _⟩ :=
    exists_stationaryFiniteCensorTimingProfile reward root 1 (by norm_num)
      hreward hnash hcontracts
  have hterminal' : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingFiniteDeadlineTimingProfile reward 1 mixed) := by
    simpa only [hzero, pow_one, mul_zero] using hterminal
  have hpay (who : ι) : quittingTerminalPayoff reward
      (quittingFiniteDeadlineTimingProfile reward 1 mixed) who =
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) who := by
    have h := hdelivery who
    simp only [hzero, pow_one, mul_zero] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  refine ⟨mixed, ?_, hpair, hpay, ?_, hterminal'⟩
  · simpa only [Nat.sub_self] using hlaws
  · intro who
    apply le_antisymm
    · unfold quittingContinuationBestResponseValue
      apply csSup_le
      · exact ⟨_, (quittingFiniteDeadlineTimingProfile reward 1 mixed) who, rfl⟩
      · rintro value ⟨deviation, rfl⟩
        simpa only [hpay who, add_zero] using hterminal' who deviation
    · rw [← hpay who]
      simpa only [Function.update_eq_self] using
        quittingTerminalPayoff_update_le_continuationBestResponseValue reward
          (quittingFiniteDeadlineTimingProfile reward 1 mixed) who
          (quittingFiniteDeadlineTimingProfile reward 1 mixed who)

end GameTheory

