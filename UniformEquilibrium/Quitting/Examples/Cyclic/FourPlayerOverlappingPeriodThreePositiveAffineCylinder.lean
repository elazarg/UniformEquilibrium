import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreeInvisibleCoordinates
import UniformEquilibrium.Quitting.Cycles.PeriodThreeClearedGapData

/-!
# An open affine reward cylinder around the overlapping period-three table

The four coordinates invisible to the displayed cycle and all of its
unilateral endpoint tests may be arbitrary.  Every other coordinate may vary
in the exact rational box and may then undergo an independent positive affine
change for its player.
-/

noncomputable section

namespace GameTheory.FourPlayerOverlappingPeriodThree

open Set

/-- Replace only the four invisible coordinates by their central values. -/
def fillInvisibleRewardCoordinatesWithCenter
    (rewardCoordinates : RewardCoordinates) : RewardCoordinates :=
  by
    classical
    exact fun row who =>
      if IsInvisibleRewardCoordinate row who then
        centralRewardCoordinates row who
      else
        rewardCoordinates row who

/-- The central fill agrees with the original table at every visible
coordinate. -/
theorem fillInvisibleRewardCoordinatesWithCenter_agrees_visible
    (rewardCoordinates : RewardCoordinates) :
    AgreeOnVisibleRewardCoordinates
      (fillInvisibleRewardCoordinatesWithCenter rewardCoordinates)
      rewardCoordinates := by
  intro row who hvisible
  simp [fillInvisibleRewardCoordinatesWithCenter, hvisible]

/-- Visible closeness to the central table becomes ordinary sixty-coordinate
closeness after filling the four invisible coordinates. -/
theorem fillInvisibleRewardCoordinatesWithCenter_distance
    (rewardCoordinates : RewardCoordinates)
    (hclose : ∀ row who, ¬ IsInvisibleRewardCoordinate row who →
      |rewardCoordinates row who - centralRewardCoordinates row who| ≤
        (1 / 50000000 : ℝ)) :
    ∀ row who,
      |fillInvisibleRewardCoordinatesWithCenter rewardCoordinates row who -
        centralRewardCoordinates row who| ≤ (1 / 50000000 : ℝ) := by
  intro row who
  by_cases hinvisible : IsInvisibleRewardCoordinate row who
  · simp [fillInvisibleRewardCoordinatesWithCenter, hinvisible]
  · simpa [fillInvisibleRewardCoordinatesWithCenter, hinvisible] using
      hclose row who hinvisible

/-- Apply an independent affine map to each player's filled reward column. -/
def playerwiseAffineFilledRewardCoordinates
    (rewardCoordinates : RewardCoordinates) (scale shift : Payoff Player) :
    RewardCoordinates :=
  fun row who => scale who *
      fillInvisibleRewardCoordinatesWithCenter rewardCoordinates row who +
    shift who

/-- Coordinate conversion commutes with the playerwise affine map. -/
theorem rewardOfCoordinates_playerwiseAffineFilled
    (rewardCoordinates : RewardCoordinates) (scale shift : Payoff Player) :
    rewardOfCoordinates
        (playerwiseAffineFilledRewardCoordinates rewardCoordinates scale shift) =
      quittingPlayerwiseAffineReward
        (rewardOfCoordinates
          (fillInvisibleRewardCoordinatesWithCenter rewardCoordinates))
        scale shift := by
  funext coalition who
  simp [rewardOfCoordinates, playerwiseAffineFilledRewardCoordinates,
    quittingPlayerwiseAffineReward]

/-- The visible part of a playerwise affine image determines a full
period-three cleared-gap data set and its phase-zero unrestricted behavioral
uniform-equilibrium payoff.  The four invisible final reward coordinates are
unrestricted. -/
theorem exists_periodThreeClearedGapData_and_uniformPayoff_of_visible_affine_reward
    (nearby final : RewardCoordinates) (scale shift : Payoff Player)
    (hnearby : ∀ row who, ¬ IsInvisibleRewardCoordinate row who →
      |nearby row who - centralRewardCoordinates row who| ≤
        (1 / 50000000 : ℝ))
    (hscale : ∀ who, 0 < scale who)
    (hfinal : ∀ row who, ¬ IsInvisibleRewardCoordinate row who →
      final row who = scale who * nearby row who + shift who) :
    ∃ point ∈ normalizedHazardCube,
      (∀ coordinate, -1 < point coordinate ∧ point coordinate < 1) ∧
      ∃ data : PeriodThreeClearedGapData (rewardOfCoordinates final),
        data.hazard = hazardOfNormalized point ∧
          (∀ phase who, who ∈ overlappingPeriodThreeSupport phase →
            quittingPeriodThreeClearedEndpointDifference
              (rewardOfCoordinates final) data.hazard phase who = 0) ∧
          (∀ phase who, who ∉ overlappingPeriodThreeSupport phase →
            quittingPeriodThreeClearedEndpointDifference
              (rewardOfCoordinates final) data.hazard phase who < 0) ∧
          (quittingGame (rewardOfCoordinates final)).IsUniformEquilibriumPayoff
            none (data.terminalPayoff 0) := by
  let filled := fillInvisibleRewardCoordinatesWithCenter nearby
  have hfilled : ∀ row who,
      |filled row who - centralRewardCoordinates row who| ≤
        (1 / 50000000 : ℝ) := by
    exact fillInvisibleRewardCoordinatesWithCenter_distance nearby hnearby
  obtain ⟨point, hpoint, hinterior, baseData, hbaseHazard,
      hactiveGaps, hinactiveGaps, _, _, _⟩ :=
    exists_overlappingPeriodThreeBlock_and_uniformPayoff_of_reward_distance
      filled hfilled
  let affineCoordinates :=
    playerwiseAffineFilledRewardCoordinates nearby scale shift
  have hrewardAffine : rewardOfCoordinates affineCoordinates =
      quittingPlayerwiseAffineReward (rewardOfCoordinates filled)
        scale shift := by
    exact rewardOfCoordinates_playerwiseAffineFilled nearby scale shift
  have hcomplementaryAffine :
      IsQuittingPeriodThreeClearedGapComplementary
        (rewardOfCoordinates affineCoordinates) (hazardOfNormalized point) := by
    rw [← hbaseHazard]
    rw [hrewardAffine]
    exact (baseData.playerwiseAffine scale shift hscale).complementary
  have hagrees : AgreeOnVisibleRewardCoordinates affineCoordinates final := by
    intro row who hvisible
    rw [hfinal row who hvisible]
    simp [affineCoordinates, playerwiseAffineFilledRewardCoordinates,
      fillInvisibleRewardCoordinatesWithCenter, hvisible]
  have hfinalComplementary :
      IsQuittingPeriodThreeClearedGapComplementary
        (rewardOfCoordinates final) (hazardOfNormalized point) := by
    apply clearedGapComplementarity_of_agree_visible
      affineCoordinates final hagrees point
    exact hcomplementaryAffine
  have hgapAffine : ∀ phase who,
      quittingPeriodThreeClearedEndpointDifference
          (rewardOfCoordinates affineCoordinates) (hazardOfNormalized point)
          phase who =
        scale who * quittingPeriodThreeClearedEndpointDifference
          (rewardOfCoordinates filled) (hazardOfNormalized point) phase who := by
    intro phase who
    rw [← hbaseHazard, hrewardAffine]
    exact quittingPeriodThreeClearedEndpointDifference_playerwiseAffine
      (rewardOfCoordinates filled) scale shift baseData.hazard
      baseData.hazard_nonneg baseData.hazard_le_one
      baseData.absorptionPositive baseData.fixedOpponentContracts phase who
  let finalData : PeriodThreeClearedGapData (rewardOfCoordinates final) :=
    { hazard := baseData.hazard
      hazard_nonneg := baseData.hazard_nonneg
      hazard_le_one := baseData.hazard_le_one
      absorptionPositive := baseData.absorptionPositive
      complementary := by
        rw [hbaseHazard]
        exact hfinalComplementary
      fixedOpponentContracts := baseData.fixedOpponentContracts }
  have hfinalActive : ∀ phase who,
      who ∈ overlappingPeriodThreeSupport phase →
        quittingPeriodThreeClearedEndpointDifference
          (rewardOfCoordinates final) finalData.hazard phase who = 0 := by
    intro phase who hsupport
    rw [show finalData.hazard = hazardOfNormalized point from hbaseHazard]
    rw [← quittingPeriodThreeClearedEndpointDifference_eq_of_agree_visible
      affineCoordinates final hagrees point phase who]
    rw [hgapAffine phase who, hactiveGaps phase who hsupport]
    ring
  have hfinalInactive : ∀ phase who,
      who ∉ overlappingPeriodThreeSupport phase →
        quittingPeriodThreeClearedEndpointDifference
          (rewardOfCoordinates final) finalData.hazard phase who < 0 := by
    intro phase who hsupport
    rw [show finalData.hazard = hazardOfNormalized point from hbaseHazard]
    rw [← quittingPeriodThreeClearedEndpointDifference_eq_of_agree_visible
      affineCoordinates final hagrees point phase who]
    rw [hgapAffine phase who]
    exact mul_neg_of_pos_of_neg (hscale who)
      (lt_trans (hinactiveGaps phase who hsupport) (by norm_num))
  refine ⟨point, hpoint, hinterior, finalData, hbaseHazard,
    hfinalActive, hfinalInactive, ?_⟩
  exact finalData.isUniformEquilibriumPayoff 0

end GameTheory.FourPlayerOverlappingPeriodThree

end
