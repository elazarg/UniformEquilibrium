/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearAlgebra.AffineResetSeries
import Research.Quitting.ORStationarizationDichotomy

/-!
# Charging failed reset-series contraction to endpoint debt

Series contraction preserves a phase-specific pin exactly when the adjacent
target shares it.  If two recurrent phases must use one fixed table slot,
the OR stationarization estimate prices precisely that adjacent target
mismatch by source and fixed-table endpoint debt.

The theorem below composes the two scalar interfaces.  It is conditional on
the already explicit common-slot and interior-mixing hypotheses; extracting
those hypotheses from one quitting chronology remains the game-facing gap.
-/

noncomputable section

namespace Research.QuittingORStationarizationDichotomy

open Math.AffineResetSeries

/-- **Contract or pay.** The absolute pin error created by contracting two
strict affine reset phases is paid by the recurrent common-slot endpoint
debt, with exactly the canonical weight of the adjacent phase. -/
theorem mixingFloor_mul_abs_seriesPinError_le_weight_mul_totalDebt
    {ι : Type*}
    {firstRatio secondRatio : ℝ}
    (hfirst1 : firstRatio < 1)
    (hsecond0 : 0 ≤ secondRatio) (hsecond1 : secondRatio < 1)
    (firstTarget secondTarget : ι → ℝ) (who : ι) (pinned : ℝ)
    (hfirstPin : firstTarget who = pinned)
    (channel : RecurrentTableChannel) (kappa : ℝ)
    (hfloor : channel.HasMixingFloor kappa) (hkappa : 0 ≤ kappa) :
    kappa *
        |resetSeriesEffectiveTarget firstRatio secondRatio
            firstTarget secondTarget who - pinned| ≤
      resetSeriesSecondWeight firstRatio secondRatio *
        channel.totalDebt pinned (secondTarget who) := by
  have hweight0 := (resetSeriesWeights_nonneg_sum_one
    hfirst1 hsecond0 hsecond1).2.1
  have hcharge := channel.mixingFloor_mul_requiredVariation_le_totalDebt
    kappa pinned (secondTarget who) hfloor hkappa
  rw [abs_resetSeriesEffectiveTarget_sub_pin
    hfirst1 hsecond0 hsecond1 firstTarget secondTarget who pinned
      hfirstPin]
  calc
    kappa * (resetSeriesSecondWeight firstRatio secondRatio *
        |secondTarget who - pinned|) =
      resetSeriesSecondWeight firstRatio secondRatio *
        (kappa * |pinned - secondTarget who|) := by
          rw [show |secondTarget who - pinned| =
            |pinned - secondTarget who| by
              rw [← abs_neg]
              congr 1
              ring]
          ring
    _ ≤ resetSeriesSecondWeight firstRatio secondRatio *
        channel.totalDebt pinned (secondTarget who) :=
      mul_le_mul_of_nonneg_left hcharge hweight0

end Research.QuittingORStationarizationDichotomy
