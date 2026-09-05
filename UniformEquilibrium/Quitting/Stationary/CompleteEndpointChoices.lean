/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Stationary.CompleteBehavioralCap
import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailProfileAdapter

/-! # Complete stationary endpoint choices, including all-Continue opponents -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Complete stationary endpoint choice, including the saturated opponent
face on which Never pays zero and Quit-now pays the singleton reward. -/
theorem exists_stationary_quitNow_or_never_completeCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    ∃ choice : Option ℕ, (choice = none ∨ choice = some 0) ∧
      quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) who
          (quittingPureTimeBehaviorStrategy reward who choice)) who =
        quittingContinuationBestResponseValue reward
          (quittingStationaryProfile reward root) who := by
  by_cases hlt : quittingStationaryFixedOpponentsContinueMass root who < 1
  · obtain ⟨choice, hend, hpay⟩ :=
      exists_quitNow_or_never_terminalPayoff_eq_unilateralCap reward root who hlt
    refine ⟨choice, hend, ?_⟩
    rw [hpay, quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap,
      quittingStationaryFullRateUnilateralCap_of_lt reward root who hlt]
  · have hmass : quittingStationaryFixedOpponentsContinueMass root who = 1 :=
      le_antisymm (quittingStationaryContinueMass_le_one _) (not_lt.mp hlt)
    rw [quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap,
      quittingStationaryFullRateUnilateralCap_of_eq_one reward root who hmass]
    by_cases hsolo : reward (quittingSingletonTerminal who) who ≤ 0
    · refine ⟨none, Or.inl rfl, ?_⟩
      rw [update_stationaryProfile_eq_update_alwaysContinue_of_fixedMass_eq_one
        reward root who _ hmass, quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue]
      change quittingTerminalPayoff reward
        (Function.update (quittingAlwaysContinueProfile reward) who
          ((quittingAlwaysContinueProfile reward) who)) who = _
      rw [Function.update_eq_self, quittingTerminalPayoff_quittingAlwaysContinue,
        max_eq_left hsolo]
    · refine ⟨some 0, Or.inr rfl, ?_⟩
      rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue,
        quittingProfileLiveRoot_stationary,
        quittingStationaryFixedOpponentsQuitValue_eq_singleton_of_mass_eq_one
          reward root who hmass, max_eq_right (not_le.mp hsolo).le]

theorem quittingCompleteCap_stationary_eq_unilateralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingContinuationBestResponseValue reward (quittingStationaryProfile reward root) who =
      quittingStationaryUnilateralCap reward root who := by
  letI : Nonempty ((quittingGame reward).BehaviorStrategy who) :=
    ⟨(quittingStationaryProfile reward root) who⟩
  apply le_antisymm
  · unfold quittingContinuationBestResponseValue
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨deviation, rfl⟩
    exact quittingTerminalPayoff_update_stationary_le_cap reward root who deviation
  · obtain ⟨deviation, hdeviation⟩ :=
      exists_quittingTerminalPayoff_update_stationary_eq_cap reward root who
    rw [← hdeviation]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue reward _ who deviation

end GameTheory
