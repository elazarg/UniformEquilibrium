/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.NormalTerminalGapConstrainedStationary
import UniformEquilibrium.Quitting.AbsorptionPath.PunishmentNormalPathStrategicSnell

/-!
# The projective-Q-bar screen on the four-player full-support residual

The normal terminal-gap construction places every hypothetical four-player
counterexample on a quantitatively full-support singleton packet.  Independently,
the punishment-normal path compiler solves the projective-Q-bar matrix chamber.
This file records their exact composition: the surviving packet lies in the
non-projective residual hard class.

This is a strict algebraic narrowing, not the missing semantic consumer.  In
particular, the residual hard-class fields still use only singleton rewards.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

/-- Same-table data retained in the four-player no-uniform-payoff branch after
both the normal terminal-gap lift and the projective-Q-bar path compiler. -/
structure FinFourQuantitativeFullSupportHardResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) where
  witness : QuittingTerminalExploitabilityWitness reward
  normalCore_eq_univ :
    normalCore (normalizedSoloMatrix reward) = Finset.univ
  all_punishmentNormal : ∀ who, IsQuittingNormalPlayer reward who
  packet : QuittingNormalizedSingletonSourcePacket reward
  packet_support_eq_univ : packet.support = Finset.univ
  massFloor_pos :
    0 < 1 / (1 + (2 * bound / witness.terminalGap) * 3)
  massFloor_le : ∀ who,
    1 / (1 + (2 * bound / witness.terminalGap) * 3) ≤ packet.mass who
  residualHardClass : ResidualHardClass reward

/-- A four-player counterexample belongs to the quantitative full-support
hard residual for every supplied coordinate bound. -/
theorem nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ S who, |reward S who| ≤ bound)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    Nonempty (FinFourQuantitativeFullSupportHardResidual reward bound) := by
  obtain ⟨witness, hcore, hnormal, packet, hsupport, hfloor, hmass⟩ :=
    exists_quantitative_fullSupport_fullNormalCore_of_finFour_of_no_uniformPayoff
      reward hreward hnot
  have hnotQBar : ¬IsProjectiveQBarMatrix (normalizedSoloMatrix reward) :=
    fun hQBar ↦ hnot
      (exists_uniformEquilibriumPayoff_of_projectiveQBar_snell reward hQBar)
  have hstandard :=
    standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff reward hnot
  exact ⟨{
    witness := witness
    normalCore_eq_univ := hcore
    all_punishmentNormal := hnormal
    packet := packet
    packet_support_eq_univ := hsupport
    massFloor_pos := hfloor
    massFloor_le := hmass
    residualHardClass := {
      normal_nonempty := hstandard.normal_nonempty
      no_homogeneous := hstandard.no_homogeneous
      normal_standardQ := hstandard.normal_standardQ
      not_full_projectiveQBar := hnotQBar } }⟩

/-- Every four-player quitting table either has a uniform-equilibrium payoff
or lies in the quantitative full-support, non-projective-Q-bar hard residual. -/
theorem uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ S who, |reward S who| ≤ bound) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      Nonempty (FinFourQuantitativeFullSupportHardResidual reward bound) := by
  by_cases hpayoff : ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff
  · exact Or.inl hpayoff
  · exact Or.inr
      (nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff
        reward hreward hpayoff)

end GameTheory
