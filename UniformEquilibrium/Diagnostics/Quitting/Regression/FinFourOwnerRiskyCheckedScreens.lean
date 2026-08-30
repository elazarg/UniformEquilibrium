/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import UniformEquilibrium.Diagnostics.Quitting.Regression.FinFourOwnerRiskyInducedOwnerMargin
import UniformEquilibrium.Diagnostics.Quitting.Regression.FinFourOwnerRiskyStationaryDebt
import UniformEquilibrium.Quitting.Examples.FinFourOwnerRiskyCapLimitRootUniqueness
import UniformEquilibrium.Quitting.Examples.FinFourOwnerRiskyPairDefect

/-!
# Checked screens of the owner-risky stationary table

This file collects the independently checked closure and exclusion facts for
the explicit owner-risky family.  The conjunction deliberately contains no
maximal-ray identification and no open reward-table neighborhood.
-/

noncomputable section

namespace GameTheory

open Math.Topology Set

namespace FinFourOwnerRiskyStationaryClosure

open QuittingSureSetOwnerRepair

/-- **Conjunctive checked-screen certificate.**  In the certified parameter
range and at positive singleton level, the family has a full-support exact
stationary certificate, zero global terminal-debt infimum, no pure sure-exit
set, the displayed paid-pair debt vector and gains, the exact induced-owner
margin, and a unique exact root at its solo cap.

This theorem does not identify a maximal cap ray and does not assert an open
reward-table neighborhood. -/
theorem checkedScreens
    (R singletonLevel : ℝ) (hR : R ∈ Icc 0 (1 / 37))
    (hlevel : 0 < singletonLevel) :
    (∃ certificate : SharpStationaryCertificate R singletonLevel,
      ∀ who, 0 < certificate.hazard who ∧ certificate.hazard who < 1) ∧
    quittingTerminalDebtSumInf (sharpReward R singletonLevel) = 0 ∧
    (∀ S : Finset Player,
      ¬ IsQuittingSureExitSet (sharpReward R singletonLevel) S) ∧
    quittingSetReward (sharpReward R singletonLevel) {0, 3} 0 -
        quittingSetReward (sharpReward R singletonLevel) {3} 0 =
      (1 / 100 : ℝ) ∧
    quittingSetReward (sharpReward R singletonLevel) {0, 1, 3} 1 -
        quittingSetReward (sharpReward R singletonLevel) {0, 3} 1 =
      (1 : ℝ) ∧
    sharpPurePairDebt R singletonLevel = ![0, 1, 1 / 100, 1] ∧
    (∀ point ∈ quittingPersistentBaseNashSet
        (sharpReward R singletonLevel) {2} {3},
      quittingInducedOwnerNeverExcess
          (sharpReward R singletonLevel) 2 {3} point = 39 / 100) ∧
    ∃! candidate : Player → PMF Bool,
      IsεQuittingRootNash (sharpReward R singletonLevel)
          (FinFourOwnerRiskyCapLimitRootUniqueness.sharpCapLimit singletonLevel)
          0 candidate := by
  refine ⟨exists_fullSupport_sharpStationaryCertificate R singletonLevel hR,
    sharpReward_quittingTerminalDebtSumInf_eq_zero R singletonLevel hR,
    not_isQuittingSureExitSet_sharpReward R singletonLevel hlevel,
    sharpMarkedGain_eq R singletonLevel,
    sharpPayerGain_eq R singletonLevel,
    sharpPurePairDebt_eq R singletonLevel, ?_, ?_⟩
  · intro point hpoint
    exact quittingInducedOwnerNeverExcess_sharpReward_eq
      R singletonLevel hpoint
  · exact
      FinFourOwnerRiskyCapLimitRootUniqueness.existsUnique_isQuittingRootNash
        R singletonLevel

end FinFourOwnerRiskyStationaryClosure

end GameTheory
