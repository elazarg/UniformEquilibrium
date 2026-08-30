/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Quitting.Examples.FinFourOwnerRiskyStationaryClosure

/-!
# Terminal-debt projection of the owner-risky stationary closure

The production example constructs an exact stationary Nash certificate.  This
Diagnostics companion projects that certificate into the global terminal-debt
infimum API without creating a production-to-Diagnostics import edge.
-/

noncomputable section

namespace GameTheory

open Math.Topology Set

namespace FinFourOwnerRiskyStationaryClosure

/-- The explicit exact stationary Nash profile forces the global literal
terminal-debt infimum of the owner-risky table to be zero. -/
theorem sharpReward_quittingTerminalDebtSumInf_eq_zero
    (R singletonLevel : ℝ) (hR : R ∈ Icc 0 (1 / 37)) :
    quittingTerminalDebtSumInf (sharpReward R singletonLevel) = 0 := by
  obtain ⟨certificate, -⟩ :=
    exists_fullSupport_sharpStationaryCertificate R singletonLevel hR
  exact quittingTerminalDebtSumInf_eq_zero_of_isZeroAsymptoticNash
    (quittingStationaryProfile (sharpReward R singletonLevel)
      (rootOfHazard certificate.hazard certificate.hazard_nonneg
        certificate.hazard_le_one))
    certificate.terminalNash

end FinFourOwnerRiskyStationaryClosure

end GameTheory
