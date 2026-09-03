import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreeEquilibrium

/-!
# Reward neighborhood for the overlapping-support period-three chart

The exact sixty-coordinate rational box is expressed directly in reward
coordinates here.  Its normalization is inverse to the affine reward chart,
so the semantic periodic compiler applies to every table in the box.
-/

noncomputable section

namespace GameTheory.FourPlayerOverlappingPeriodThree

open Set

/-- The central rational reward table in row coordinates. -/
def centralRewardCoordinates : RewardCoordinates :=
  fun row who => overlappingPeriodThreeRewardRow row who

/-- Flattening a reward row and player agrees with the standard finite-product
coordinate equivalence. -/
theorem rewardParameterIndex_eq_finProdFinEquiv
    (row : RewardRow) (who : Player) :
    rewardParameterIndex row who = finProdFinEquiv (row, who) := by
  apply Fin.ext
  simp [rewardParameterIndex, finProdFinEquiv]
  omega

/-- Normalize an arbitrary sixty-coordinate reward table around the displayed
rational center. -/
def normalizedParameterOfRewardCoordinates
    (rewardCoordinates : RewardCoordinates) : Fin 60 → ℝ :=
  fun coordinate =>
    let rowPlayer := finProdFinEquiv.symm coordinate
    (rewardCoordinates rowPlayer.1 rowPlayer.2 -
      centralRewardCoordinates rowPlayer.1 rowPlayer.2) / rewardRadius

@[simp] theorem normalizedParameterOfRewardCoordinates_rewardParameterIndex
    (rewardCoordinates : RewardCoordinates)
    (row : RewardRow) (who : Player) :
    normalizedParameterOfRewardCoordinates rewardCoordinates
        (rewardParameterIndex row who) =
      (rewardCoordinates row who - centralRewardCoordinates row who) /
        rewardRadius := by
  rw [rewardParameterIndex_eq_finProdFinEquiv]
  simp [normalizedParameterOfRewardCoordinates]

@[simp] theorem rewardCoordinatesOfNormalizedParameter_inverse
    (rewardCoordinates : RewardCoordinates) :
    rewardCoordinatesOfNormalizedParameter
        (normalizedParameterOfRewardCoordinates rewardCoordinates) =
      rewardCoordinates := by
  funext row who
  simp [rewardCoordinatesOfNormalizedParameter,
    centralRewardCoordinates, rewardRadius]
  ring

/-- Coordinatewise distance at most `1/50000000` from the rational table is
exactly enough to place the normalized parameters in the certified cube. -/
theorem normalizedParameter_mem_cube_of_reward_distance
    (rewardCoordinates : RewardCoordinates)
    (hclose : ∀ row who,
      |rewardCoordinates row who - centralRewardCoordinates row who| ≤
        (rewardRadius : ℝ)) :
    normalizedParameterOfRewardCoordinates rewardCoordinates ∈
      normalizedRewardParameterCube := by
  constructor <;> intro coordinate
  · let rowPlayer : RewardRow × Player := finProdFinEquiv.symm coordinate
    have hbound := (abs_le.mp (hclose rowPlayer.1 rowPlayer.2)).1
    change -1 ≤
      (rewardCoordinates rowPlayer.1 rowPlayer.2 -
        centralRewardCoordinates rowPlayer.1 rowPlayer.2) / rewardRadius
    have hradius : (0 : ℝ) < rewardRadius := by norm_num [rewardRadius]
    rw [le_div_iff₀ hradius]
    simpa only [neg_mul, one_mul] using hbound
  · let rowPlayer : RewardRow × Player := finProdFinEquiv.symm coordinate
    have hbound := (abs_le.mp (hclose rowPlayer.1 rowPlayer.2)).2
    change
      (rewardCoordinates rowPlayer.1 rowPlayer.2 -
        centralRewardCoordinates rowPlayer.1 rowPlayer.2) / rewardRadius ≤ 1
    have hradius : (0 : ℝ) < rewardRadius := by norm_num [rewardRadius]
    rw [div_le_iff₀ hradius]
    simpa only [one_mul] using hbound

/-- Every reward table in the literal sixty-coordinate radius
`1/50000000` has an exact absorbing overlapping-support period-three
block and a fixed phase-zero uniform-equilibrium payoff against
unrestricted behavioral deviations. -/
theorem exists_overlappingPeriodThreeBlock_and_uniformPayoff_of_reward_distance
    (rewardCoordinates : RewardCoordinates)
    (hclose : ∀ row who,
      |rewardCoordinates row who - centralRewardCoordinates row who| ≤
        (1 / 50000000 : ℝ)) :
    ∃ point ∈ normalizedHazardCube,
      (∀ coordinate, -1 < point coordinate ∧ point coordinate < 1) ∧
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
  let parameter :=
    normalizedParameterOfRewardCoordinates rewardCoordinates
  have hparameter : parameter ∈ normalizedRewardParameterCube := by
    apply normalizedParameter_mem_cube_of_reward_distance
    intro row who
    have hradius : (rewardRadius : ℝ) = 1 / 50000000 := by
      norm_num [rewardRadius]
    rw [hradius]
    exact hclose row who
  have hresult :=
    exists_overlappingPeriodThreeBlock_and_phaseZero_uniformEquilibriumPayoff
      parameter hparameter
  rw [rewardCoordinatesOfNormalizedParameter_inverse] at hresult
  exact hresult

/-- The displayed rational table itself has the exact period-three
block and fixed phase-zero unrestricted uniform-equilibrium payoff. -/
theorem overlappingPeriodThreeReward_has_block_and_uniformPayoff :
    ∃ point ∈ normalizedHazardCube,
      (∀ coordinate, -1 < point coordinate ∧ point coordinate < 1) ∧
      let hazard := hazardOfNormalized point
      ∃ data : PeriodThreeClearedGapData overlappingPeriodThreeReward,
        data.hazard = hazard ∧
        (∀ phase who, who ∈ overlappingPeriodThreeSupport phase →
          quittingPeriodThreeClearedEndpointDifference
            overlappingPeriodThreeReward hazard phase who = 0) ∧
        (∀ phase who, who ∉ overlappingPeriodThreeSupport phase →
          quittingPeriodThreeClearedEndpointDifference
            overlappingPeriodThreeReward hazard phase who < (-29 / 100 : ℝ)) ∧
        (9 / 10 : ℝ) < quittingPeriodThreeAbsorptionDenominator hazard ∧
        quittingPeriodThreeAbsorptionDenominator hazard < (19 / 20 : ℝ) ∧
        (quittingGame overlappingPeriodThreeReward).IsUniformEquilibriumPayoff none
          (data.terminalPayoff 0) := by
  have hclose : ∀ row who,
      |centralRewardCoordinates row who - centralRewardCoordinates row who| ≤
        (1 / 50000000 : ℝ) := by
    intro row who
    norm_num
  have hresult :=
    exists_overlappingPeriodThreeBlock_and_uniformPayoff_of_reward_distance
      centralRewardCoordinates hclose
  have hreward : rewardOfCoordinates centralRewardCoordinates = overlappingPeriodThreeReward := by
    rfl
  rw [hreward] at hresult
  exact hresult

end GameTheory.FourPlayerOverlappingPeriodThree

end
