/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticForcedOwnerWallRectangleCurvature
import UniformEquilibrium.Quitting.Debt.Dynamic.DebtOwnerTransferCounterexample

/-!
# Positive action support does not transport a forced-Continue-face loss

The final observer-absent residual cannot be closed merely by assuming that
the selected outsider action has probability bounded away from zero.  The
existing two-player debt-transfer table already gives the sharp local
regression.

Both players use the fair root.  The outsider is exactly indifferent at the
actual source, so neither pure action has positive source gain and the root is
exact endpoint Nash.  After forcing the owner to Continue, however, the
outsider's pure-Quit gain is `-1/2`.  The selected action still has probability
`1/2`, and its owner/outsider rectangle is `1`: the owner-Quit contribution
cancels the entire face loss when returning to the actual source.

Thus even full support supplies no legal source-matched gain.  A consumer of
`quittingFiniteForcedOwnerContinueFaceLossOccupation` needs an additional
signed source-transport premise; an action-support lower bound alone is not
enough.  This is a local quitting regression, not a terminal exploitability witness
construction.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace ForcedOwnerContinueFaceLossSupportNoGo

open QuittingDynamicDebtOwnerTransferCounterexample

abbrev owner : Bool := false
abbrev outsider : Bool := true

def ownerContinueRoot : Bool → PMF Bool :=
  Function.update root owner (PMF.pure false)

def ownerQuitRoot : Bool → PMF Bool :=
  Function.update root owner (PMF.pure true)

@[simp] theorem outsider_quitProbability :
    (root outsider true).toReal = 1 / 2 := by
  norm_num [root, outsider, PMF.uniformOfFintype_apply]

@[simp] theorem outsider_continueProbability :
    (root outsider false).toReal = 1 / 2 := by
  norm_num [root, outsider, PMF.uniformOfFintype_apply]

theorem actual_pureQuit_gain_eq_zero :
    quittingRootDeviationGain reward (0 : Payoff Bool) root outsider
        (PMF.pure true) = 0 := by
  rw [quittingRootDeviationGain_pure_true_eq]
  unfold quittingRootEndpointDifference
  rw [true_quitPayoff, true_continuePayoff]
  ring

theorem actual_pureContinue_gain_eq_zero :
    quittingRootDeviationGain reward (0 : Payoff Bool) root outsider
        (PMF.pure false) = 0 := by
  rw [quittingRootDeviationGain_pure_false_eq]
  unfold quittingRootEndpointDifference
  rw [true_quitPayoff, true_continuePayoff]
  ring

theorem ownerContinue_outsider_quitPayoff_eq_neg_one :
    quittingRootQuitPayoff reward (0 : Payoff Bool) ownerContinueRoot
        outsider = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff ownerContinueRoot
  rw [QuittingDynamicDebtOwnerTransferCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [root, PMF.uniformOfFintype_apply, quittingRootPayoff, reward,
    QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction,
    owner, outsider]

theorem ownerContinue_outsider_continuePayoff_eq_zero :
    quittingRootContinuePayoff reward (0 : Payoff Bool) ownerContinueRoot
        outsider = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff ownerContinueRoot
  rw [QuittingDynamicDebtOwnerTransferCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [root, PMF.uniformOfFintype_apply, quittingRootPayoff, reward,
    QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction,
    owner, outsider]

theorem ownerContinue_pureQuit_gain_eq_neg_half :
    quittingRootDeviationGain reward (0 : Payoff Bool) ownerContinueRoot
        outsider (PMF.pure true) = -(1 / 2 : ℝ) := by
  rw [quittingRootDeviationGain_pure_true_eq]
  unfold quittingRootEndpointDifference
  rw [ownerContinue_outsider_quitPayoff_eq_neg_one,
    ownerContinue_outsider_continuePayoff_eq_zero]
  norm_num [ownerContinueRoot, root, outsider,
    PMF.uniformOfFintype_apply]

theorem ownerQuit_outsider_quitPayoff_eq_one :
    quittingRootQuitPayoff reward (0 : Payoff Bool) ownerQuitRoot outsider =
      1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff ownerQuitRoot
  rw [QuittingDynamicDebtOwnerTransferCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [root, PMF.uniformOfFintype_apply, quittingRootPayoff, reward,
    QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction,
    owner, outsider]

theorem ownerQuit_outsider_continuePayoff_eq_zero :
    quittingRootContinuePayoff reward (0 : Payoff Bool) ownerQuitRoot outsider =
      0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff ownerQuitRoot
  rw [QuittingDynamicDebtOwnerTransferCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [root, PMF.uniformOfFintype_apply, quittingRootPayoff, reward,
    QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction,
    owner, outsider]

theorem ownerQuit_pureQuit_gain_eq_half :
    quittingRootDeviationGain reward (0 : Payoff Bool) ownerQuitRoot outsider
        (PMF.pure true) = 1 / 2 := by
  rw [quittingRootDeviationGain_pure_true_eq]
  unfold quittingRootEndpointDifference
  rw [ownerQuit_outsider_quitPayoff_eq_one,
    ownerQuit_outsider_continuePayoff_eq_zero]
  norm_num [ownerQuitRoot, root, outsider, PMF.uniformOfFintype_apply]

theorem positive_quit_rectangle_eq_one :
    quittingOwnerOutsiderDeviationRectangle reward (0 : Payoff Bool) root
        owner outsider true = 1 := by
  unfold quittingOwnerOutsiderDeviationRectangle
  rw [show Function.update root owner (PMF.pure true) = ownerQuitRoot by rfl,
    show Function.update root owner (PMF.pure false) = ownerContinueRoot by rfl,
    ownerQuit_pureQuit_gain_eq_half,
    ownerContinue_pureQuit_gain_eq_neg_half]
  ring

/-- The exact support/transport obstruction in one packet.  The selected
action has probability `1/2`, its forced-Continue-face loss is `1/2`, and the
rectangle is positive, but both actual pure deviations have gain zero and the
actual root is exact endpoint Nash. -/
theorem positiveSupport_faceLoss_without_sourceGain :
    (root outsider true).toReal = 1 / 2 ∧
    max (-quittingRootDeviationGain reward (0 : Payoff Bool)
      ownerContinueRoot outsider (PMF.pure true)) 0 = 1 / 2 ∧
    quittingOwnerOutsiderDeviationRectangle reward (0 : Payoff Bool) root
      owner outsider true = 1 ∧
    quittingRootDeviationGain reward (0 : Payoff Bool) root outsider
      (PMF.pure true) = 0 ∧
    quittingRootDeviationGain reward (0 : Payoff Bool) root outsider
      (PMF.pure false) = 0 ∧
    IsεQuittingRootEndpointNash reward (0 : Payoff Bool) 0 root := by
  refine ⟨outsider_quitProbability, ?_, positive_quit_rectangle_eq_one,
    actual_pureQuit_gain_eq_zero, actual_pureContinue_gain_eq_zero,
    root_isEndpointNash_zero⟩
  rw [ownerContinue_pureQuit_gain_eq_neg_half]
  norm_num

/-- Numerically, the owner-Quit interaction pays exactly the entire selected
face loss.  This is why the opposite face action has no gain after transport
back to the source. -/
theorem supportWeighted_faceLoss_eq_ownerInteraction :
    (root outsider true).toReal *
        max (-quittingRootDeviationGain reward (0 : Payoff Bool)
          ownerContinueRoot outsider (PMF.pure true)) 0 =
      (root owner true).toReal * (root outsider true).toReal *
        max (quittingOwnerOutsiderDeviationRectangle reward
          (0 : Payoff Bool) root owner outsider true) 0 := by
  rw [ownerContinue_pureQuit_gain_eq_neg_half,
    positive_quit_rectangle_eq_one]
  norm_num [root, owner, outsider, PMF.uniformOfFintype_apply]

end ForcedOwnerContinueFaceLossSupportNoGo

end GameTheory
