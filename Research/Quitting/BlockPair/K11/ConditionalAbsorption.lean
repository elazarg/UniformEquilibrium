import Research.Quitting.BlockPair.K11.ConditionalBlockData

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.ProbabilityMassFunction

/-- Every interior K11 hazard vector has positive absorption already at phase
zero, because player zero is an active coordinate there. -/
theorem phaseRoot_zero_positive_absorption
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1) :
    0 < quittingRootAbsorptionMass (phaseRoot x hx 0) := by
  have hfactor : ((phaseRoot x hx 0 0) false).toReal < 1 := by
    rw [phaseRoot_false]
    change 1 - x 0 < 1
    linarith [(hx 0).1]
  have hmass := quittingStationaryContinueMass_eq_forcedContinue_mul_own
    (phaseRoot x hx 0) 0
  have hforcedNonneg := quittingStationaryContinueMass_nonneg
    (Function.update (phaseRoot x hx 0) 0 (PMF.pure false))
  have hforcedLeOne := quittingStationaryContinueMass_le_one
    (Function.update (phaseRoot x hx 0) 0 (PMF.pure false))
  have hfactorNonneg : 0 ≤ ((phaseRoot x hx 0 0) false).toReal :=
    ENNReal.toReal_nonneg
  unfold quittingRootAbsorptionMass
  rw [hmass]
  nlinarith

theorem exists_phaseRoot_positive_absorption
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1) :
    ∃ phase, 0 < quittingRootAbsorptionMass (phaseRoot x hx phase) :=
  ⟨0, phaseRoot_zero_positive_absorption x hx⟩

end GameTheory.BlockPairK11.ConditionalData
