/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.FullRateStationaryVerifier

/-!
# Complete behavioral caps at stationary quitting roots

The full-rate stationary unilateral cap is not merely an upper verifier.  It
is exactly the supremum over all complete behavioral deviations.  Under
strict opponent contraction, the two literal endpoint strategies, immediate
Quit and Never, attain the endpoints whose maximum is that complete cap.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The full-rate stationary cap is exactly the supremum over every complete
behavioral deviation against the displayed stationary opponents. -/
theorem quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward root) who =
      quittingStationaryFullRateUnilateralCap reward root who := by
  apply le_antisymm
  · unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, (quittingStationaryProfile reward root) who, rfl⟩
    · rintro value ⟨deviation, rfl⟩
      exact quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap
        reward root who deviation
  · obtain ⟨deviation, hdeviation⟩ :=
      exists_behaviorStrategy_terminalPayoff_eq_fullRateUnilateralCap
        reward root who
    rw [← hdeviation]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (quittingStationaryProfile reward root) who deviation

/-- If the opponents contract, the complete behavioral cap is the maximum of
the payoffs of the literal immediate-Quit and Never behavior strategies. -/
theorem quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hcontracts :
      quittingStationaryFixedOpponentsContinueMass root who < 1) :
    quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward root) who =
      max
        (quittingTerminalPayoff reward
          (Function.update (quittingStationaryProfile reward root) who
            (quittingPureTimeBehaviorStrategy reward who (some 0))) who)
        (quittingTerminalPayoff reward
          (Function.update (quittingStationaryProfile reward root) who
            (quittingPureTimeBehaviorStrategy reward who none)) who) := by
  rw [quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap,
    quittingStationaryFullRateUnilateralCap_of_lt reward root who hcontracts]
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingProfileLiveRoot_stationary,
    quittingRootSequencePureTimeTerminalValue_const reward root who hcontracts
      (some 0),
    quittingRootSequencePureTimeTerminalValue_const reward root who hcontracts
      none]
  simp [quittingStationaryDeterministicValue,
    quittingStationaryPureTimeValue]

end GameTheory
