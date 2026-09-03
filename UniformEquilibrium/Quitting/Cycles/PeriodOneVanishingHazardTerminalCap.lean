/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PeriodOneVanishingHazardLimitLaw
import UniformEquilibrium.Quitting.Stationary.CompleteBehavioralCap

/-!
# Complete terminal caps of selected one-period sources

Every selected root in an interior one-period source has strictly contracting
opponents.  Consequently the complete behavioral best-response supremum at
each actual selected profile is exactly the maximum of the literal immediate
Quit and Never endpoint payoffs.

This exact finite-source envelope does not yet identify the limits of the two
endpoint payoffs or select which endpoint is eventually optimal.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℕ → ℝ}
  {source : PeriodOneVanishingHazardSource reward error}

namespace PeriodOneNormalizedSourceLimit

/-- Every player's opponents contract at every actual selected one-period
source. -/
theorem selectedFixedOpponentsContinueMass_lt_one
    (limit : PeriodOneNormalizedSourceLimit source)
    (index : ℕ) (who : ι) :
    quittingStationaryFixedOpponentsContinueMass
        (source.root (limit.select index)) who < 1 := by
  simpa [PeriodOneVanishingHazardSource.root,
    PeriodOneNormalizedSourceLimit.originalIndex] using
    (InteriorApproximateNashCyclicBlock.prod_fixedOpponentsContinueMass_lt_one
        (source.block (limit.originalIndex index)) who)

/-- At every actual selected source, the complete behavioral cap is exactly
the maximum of the literal immediate-Quit and Never endpoint payoffs. -/
theorem selectedCompleteBehavioralCap_eq_max_quitNow_never
    (limit : PeriodOneNormalizedSourceLimit source)
    (index : ℕ) (who : ι) :
    quittingContinuationBestResponseValue reward
        (source.profile (limit.select index)) who =
      max
        (quittingTerminalPayoff reward
          (Function.update (source.profile (limit.select index)) who
            (quittingPureTimeBehaviorStrategy reward who (some 0))) who)
        (quittingTerminalPayoff reward
          (Function.update (source.profile (limit.select index)) who
            (quittingPureTimeBehaviorStrategy reward who none)) who) := by
  rw [limit.selectedProfile_eq_stationary index]
  exact
    quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never
      reward (source.root (limit.select index)) who
        (limit.selectedFixedOpponentsContinueMass_lt_one index who)

end PeriodOneNormalizedSourceLimit

end GameTheory
