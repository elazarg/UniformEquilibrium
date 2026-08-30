/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import Research.Quitting.FinFourMaximalRayZeroMinimumRegressions
import UniformEquilibrium.Diagnostics.Quitting.Regression.FinFourOwnerRiskyStationaryDebt

/-!
# Research aliases for older maximal-ray safe chambers

The production owner-risky stationary table is separate from the two older
maximal-ray tables below.  These thin aliases retain the latter tables' literal
pure-singleton chambers without identifying any of the three reward families.
-/

noncomputable section

namespace GameTheory
namespace FinFourHopfConcreteChambers

open FinFourMaximalRayZeroMinimumRegressions
open FinFourOwnerRiskyStationaryClosure
open Math.Topology Set

abbrev Player := Fin 4

/-- Thin alias for the rational table's safe singleton owned by player two. -/
theorem rationalSingletonTwoChamber :
    QuittingPureSingletonChamber (rationalReward rationalScale) 2 :=
  rationalPureSingletonChamber

/-- Thin alias for the full-binding table's safe singleton owned by player
two.  This is not the production owner-risky stationary table. -/
theorem fullBindingSingletonTwoChamber (R : ℝ) :
    QuittingPureSingletonChamber (fullBindingReward R rationalScale) 2 :=
  fullBindingPureSingletonChamber R

/-! ## Owner-risky specialization at the canonical full-binding scale -/

/-- The canonical full-binding scale lies in the stationary table's certified
parameter interval. -/
theorem fullBindingInitialCap_mem_sharpRange :
    fullBindingInitialCap ∈ Icc (0 : ℝ) (1 / 37) :=
  ⟨fullBindingInitialCap_pos.le, fullBindingInitialCap_le⟩

/-- At the canonical full-binding scale, every singleton level has an actual
full-support stationary exact Nash certificate for the owner-risky table. -/
theorem exists_fullSupport_sharpStationaryCertificate_fullBindingInitialCap
    (singletonLevel : ℝ) :
    ∃ certificate :
        SharpStationaryCertificate fullBindingInitialCap singletonLevel,
      ∀ who, 0 < certificate.hazard who ∧ certificate.hazard who < 1 :=
  exists_fullSupport_sharpStationaryCertificate
    fullBindingInitialCap singletonLevel fullBindingInitialCap_mem_sharpRange

/-- At the canonical full-binding scale, the owner-risky table has zero global
terminal-debt infimum. -/
theorem sharpReward_fullBindingInitialCap_quittingTerminalDebtSumInf_eq_zero
    (singletonLevel : ℝ) :
    quittingTerminalDebtSumInf
      (sharpReward fullBindingInitialCap singletonLevel) = 0 :=
  sharpReward_quittingTerminalDebtSumInf_eq_zero
    fullBindingInitialCap singletonLevel fullBindingInitialCap_mem_sharpRange

end FinFourHopfConcreteChambers
end GameTheory
