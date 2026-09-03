import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreeSemanticBridge
import UniformEquilibrium.Quitting.Cycles.PeriodThreeClearedGapData

/-!
# Uniform payoff from the overlapping-support period-three chart

This file assembles the exact active equalities, strict inactive inequalities,
positive absorption, and player-deleted contraction into the unrestricted
behavioral periodic compiler at initial phase zero.
-/

noncomputable section

namespace GameTheory.FourPlayerOverlappingPeriodThree

open Set
open Math.Interval Math.Interval.RationalPolynomial

theorem exists_inactiveSlot_of_not_mem_overlappingPeriodThreeSupport
    (phase : Fin 3) (who : Player)
    (hnot : who ∉ overlappingPeriodThreeSupport phase) :
    ∃ slot : InactiveSlot, inactivePhasePlayer slot = (phase, who) := by
  fin_cases phase <;> fin_cases who <;>
    simp [overlappingPeriodThreeSupport] at hnot ⊢
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- Every normalized reward parameter in the verified sixty-dimensional
cube has an exact absorbing overlapping-support period-three block and
a phase-zero uniform-equilibrium payoff against unrestricted behavioral
deviations. -/
theorem exists_overlappingPeriodThreeBlock_and_phaseZero_uniformEquilibriumPayoff
    (parameter : Fin 60 → ℝ)
    (hparameter : parameter ∈ normalizedRewardParameterCube) :
    ∃ point ∈ normalizedHazardCube,
      (∀ coordinate, -1 < point coordinate ∧ point coordinate < 1) ∧
      let rewardCoordinates :=
        rewardCoordinatesOfNormalizedParameter parameter
      let semanticReward := rewardOfCoordinates rewardCoordinates
      let hazard := hazardOfNormalized point
      ∃ data : PeriodThreeClearedGapData semanticReward,
        data.hazard = hazard ∧
        (∀ phase who, who ∈ overlappingPeriodThreeSupport phase →
          quittingPeriodThreeClearedEndpointDifference
            semanticReward hazard phase who = 0) ∧
        (∀ phase who, who ∉ overlappingPeriodThreeSupport phase →
          quittingPeriodThreeClearedEndpointDifference
            semanticReward hazard phase who < (-29 / 100 : ℝ)) ∧
        (9 / 10 : ℝ) < quittingPeriodThreeAbsorptionDenominator hazard ∧
        quittingPeriodThreeAbsorptionDenominator hazard < (19 / 20 : ℝ) ∧
        (quittingGame semanticReward).IsUniformEquilibriumPayoff none
          (data.terminalPayoff 0) := by
  obtain ⟨point, hpoint, hinterior, hactive⟩ :=
    exists_interior_activeResidual_zero parameter hparameter
  have hfull := leadingCoordinatePoint_mem_fullNormalizedCoordinateBox
    point parameter hpoint hparameter
  let semanticReward := rewardOfCoordinates
    (rewardCoordinatesOfNormalizedParameter parameter)
  let hazard := hazardOfNormalized point
  have h0 : ∀ phase who, 0 ≤ hazard phase who := fun phase who ↦
    (hazardOfNormalized_mem_unitInterval hpoint phase who).1
  have h1 : ∀ phase who, hazard phase who ≤ 1 := fun phase who ↦
    (hazardOfNormalized_mem_unitInterval hpoint phase who).2
  have hdenominatorBounds :
      (9 / 10 : ℝ) < quittingPeriodThreeAbsorptionDenominator hazard ∧
        quittingPeriodThreeAbsorptionDenominator hazard < (19 / 20 : ℝ) := by
    have hbounds := denominator_strict_bounds
      (leadingCoordinatePoint point parameter) hfull
    rw [evalReal_leadingCoordinatePoint_denominatorExpression] at hbounds
    exact hbounds
  have hdenominator :
      0 < quittingPeriodThreeAbsorptionDenominator hazard :=
    (by norm_num : (0 : ℝ) < 9 / 10) |>.trans hdenominatorBounds.1
  have hactiveGaps : ∀ phase who,
      who ∈ overlappingPeriodThreeSupport phase →
        quittingPeriodThreeClearedEndpointDifference
          semanticReward hazard phase who = 0 := by
    intro phase who hsupport
    obtain ⟨coordinate, hcoordinate⟩ :=
      (activeSlot_is_enumerated_iff_mem_overlappingPeriodThreeSupport
        phase who).mpr hsupport
    have hzero := hactive coordinate
    rw [activeResidualExpression, hcoordinate,
      evalReal_supportedClearedGapExpression_eq_semantic] at hzero
    exact hzero
  have hinactiveGaps : ∀ phase who,
      who ∉ overlappingPeriodThreeSupport phase →
        quittingPeriodThreeClearedEndpointDifference
          semanticReward hazard phase who < (-29 / 100 : ℝ) := by
    intro phase who hsupport
    obtain ⟨slot, hslot⟩ :=
      exists_inactiveSlot_of_not_mem_overlappingPeriodThreeSupport
        phase who hsupport
    have hstrict :=
      inactiveClearedGap_lt_negative_twenty_nine_hundredths
        (leadingCoordinatePoint point parameter) hfull slot
    rw [evalReal_supportedClearedGapExpression_eq_semantic] at hstrict
    rw [hslot] at hstrict
    exact hstrict
  have hcomplementary :
      IsQuittingPeriodThreeClearedGapComplementary semanticReward hazard := by
    intro phase who
    by_cases hsupport : who ∈ overlappingPeriodThreeSupport phase
    · have hgap := hactiveGaps phase who hsupport
      simp [hgap]
    · have hhazard : hazard phase who = 0 := by
        apply le_antisymm
        · exact le_of_not_gt fun hpositive ↦ hsupport
            ((hazardOfNormalized_pos_iff_mem_support hpoint phase who).mp
              hpositive)
        · exact h0 phase who
      have hgap : quittingPeriodThreeClearedEndpointDifference
          semanticReward hazard phase who < 0 := by
        exact (hinactiveGaps phase who hsupport).trans_le (by norm_num)
      constructor
      · simpa [hhazard] using hgap.le
      · simp [hhazard]
  have hcontracts : ∀ who,
      (∏ phase : Fin 3,
        quittingStationaryFixedOpponentsContinueMass
          (quittingBlockCycle hazard h0 h1 phase) who) < 1 := by
    simpa [hazard] using hazardOfNormalized_fixedOpponentContraction hpoint
  let data : PeriodThreeClearedGapData semanticReward :=
    { hazard := hazard
      hazard_nonneg := h0
      hazard_le_one := h1
      absorptionPositive := hdenominator
      complementary := hcomplementary
      fixedOpponentContracts := hcontracts }
  refine ⟨point, hpoint, hinterior, data, rfl, hactiveGaps,
    hinactiveGaps, hdenominatorBounds.1, hdenominatorBounds.2, ?_⟩
  exact data.isUniformEquilibriumPayoff 0

end GameTheory.FourPlayerOverlappingPeriodThree

end
