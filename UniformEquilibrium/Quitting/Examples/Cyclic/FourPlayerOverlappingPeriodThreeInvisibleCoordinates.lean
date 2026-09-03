import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreeRewardNeighborhood

/-!
# Reward coordinates invisible to the overlapping period-three cycle

Four reward coordinates cannot be reached either on path or by a unilateral
deviation from the displayed support word.  This file states that fact
literally at the immediate, endpoint, window, and cleared-gap levels.
-/

noncomputable section

namespace GameTheory.FourPlayerOverlappingPeriodThree

/-- The four player/coalition coordinates absent from every on-path or
one-player-deviation endpoint of the overlapping support word. -/
def IsInvisibleRewardCoordinate (row : RewardRow) (who : Player) : Prop :=
  (who = 0 ∧ (row = 13 ∨ row = 14)) ∨
    (who = 3 ∧ (row = 6 ∨ row = 14))

/-- The invisible set is exactly the two listed rows for player zero and the
two listed rows for player three. -/
theorem isInvisibleRewardCoordinate_iff (row : RewardRow) (who : Player) :
    IsInvisibleRewardCoordinate row who ↔
      (who = 0 ∧ (row = 13 ∨ row = 14)) ∨
        (who = 3 ∧ (row = 6 ∨ row = 14)) := by
  rfl

/-- Two reward tables agree on every coordinate visible to the period-three
cycle and its unilateral endpoint tests. -/
def AgreeOnVisibleRewardCoordinates
    (first second : RewardCoordinates) : Prop :=
  ∀ row who, ¬ IsInvisibleRewardCoordinate row who →
    first row who = second row who

theorem supportRow_is_visible
    (phase : Fin 3) (row : RewardRow) (who : Player)
    (hrow : row ∈ supportRows phase) :
    ¬ IsInvisibleRewardCoordinate row who := by
  fin_cases phase <;> fin_cases row <;> fin_cases who <;>
    simp [supportRows, IsInvisibleRewardCoordinate] at hrow ⊢

theorem pureQuitRow_is_visible
    (phase : Fin 3) (who : Player) (row : RewardRow)
    (hrow : row ∈ pureQuitRows phase who) :
    ¬ IsInvisibleRewardCoordinate row who := by
  fin_cases phase <;> fin_cases who <;> fin_cases row <;>
    simp [pureQuitRows, IsInvisibleRewardCoordinate] at hrow ⊢

theorem excludedRow_is_visible
    (phase : Fin 3) (who : Player) (row : RewardRow)
    (hrow : row ∈ excludedRows phase who) :
    ¬ IsInvisibleRewardCoordinate row who := by
  fin_cases phase <;> fin_cases who <;> fin_cases row <;>
    simp [excludedRows, IsInvisibleRewardCoordinate] at hrow ⊢

/-- The unconditional immediate contribution is unchanged by overwriting the
four invisible coordinates. -/
theorem quittingPeriodThreeImmediateContribution_eq_of_agree_visible
    (first second : RewardCoordinates)
    (hagrees : AgreeOnVisibleRewardCoordinates first second)
    (point : HazardCoordinate → ℝ) (phase : Fin 3) (who : Player) :
    quittingPeriodThreeImmediateContribution (rewardOfCoordinates first)
        (hazardOfNormalized point) phase who =
      quittingPeriodThreeImmediateContribution (rewardOfCoordinates second)
        (hazardOfNormalized point) phase who := by
  rw [quittingPeriodThreeImmediateContribution_eq_sum_rows,
    quittingPeriodThreeImmediateContribution_eq_sum_rows]
  apply Finset.sum_congr rfl
  intro row _
  by_cases hrow : row ∈ supportRows phase
  · rw [hagrees row who (supportRow_is_visible phase row who hrow)]
  · rw [coalitionMass_coalitionOfRow_eq_zero_of_not_mem_supportRows
      point phase row hrow]
    simp

/-- Every sure-Quit endpoint value is unchanged by overwriting the four
invisible coordinates. -/
theorem sigmaValue_eq_of_agree_visible
    (first second : RewardCoordinates)
    (hagrees : AgreeOnVisibleRewardCoordinates first second)
    (point : HazardCoordinate → ℝ) (phase : Fin 3) (who : Player) :
    sigmaValue (weightOfReward (rewardOfCoordinates first))
        (hazardOfNormalized point phase) who =
      sigmaValue (weightOfReward (rewardOfCoordinates second))
        (hazardOfNormalized point phase) who := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum,
    sigmaValue_eq_pureQuitEndpointRowSum]
  unfold pureQuitEndpointRowSum
  apply Finset.sum_congr rfl
  intro row _
  by_cases hmember : who ∈ coalitionOfRow row
  · simp only [if_pos hmember]
    by_cases hrow : row ∈ pureQuitRows phase who
    · rw [weightOfReward_rewardOfCoordinates_coalitionOfRow,
        weightOfReward_rewardOfCoordinates_coalitionOfRow,
        hagrees row who (pureQuitRow_is_visible phase who row hrow)]
    · rw [opponentCoalitionMass_eq_zero_of_pureQuitRow_not_supported
        point phase who row hmember hrow]
      simp
  · simp [hmember]

/-- Every pure-Continue absorbing contribution is unchanged by overwriting
the four invisible coordinates. -/
theorem excludedValue_eq_of_agree_visible
    (first second : RewardCoordinates)
    (hagrees : AgreeOnVisibleRewardCoordinates first second)
    (point : HazardCoordinate → ℝ) (phase : Fin 3) (who : Player) :
    excludedValue (weightOfReward (rewardOfCoordinates first))
        (hazardOfNormalized point phase) who =
      excludedValue (weightOfReward (rewardOfCoordinates second))
        (hazardOfNormalized point phase) who := by
  rw [excludedValue_eq_excludedEndpointRowSum,
    excludedValue_eq_excludedEndpointRowSum]
  unfold excludedEndpointRowSum
  apply Finset.sum_congr rfl
  intro row _
  by_cases hnotMember : who ∉ coalitionOfRow row
  · simp only [if_pos hnotMember]
    by_cases hrow : row ∈ excludedRows phase who
    · rw [weightOfReward_rewardOfCoordinates_coalitionOfRow,
        weightOfReward_rewardOfCoordinates_coalitionOfRow,
        hagrees row who (excludedRow_is_visible phase who row hrow)]
    · rw [opponentCoalitionMass_eq_zero_of_excludedRow_not_supported
        point phase who row hnotMember hrow]
      simp
  · simp only [if_neg hnotMember]

/-- Every three-phase immediate reward window is unchanged by overwriting the
four invisible coordinates. -/
theorem quittingPeriodThreeImmediateWindow_eq_of_agree_visible
    (first second : RewardCoordinates)
    (hagrees : AgreeOnVisibleRewardCoordinates first second)
    (point : HazardCoordinate → ℝ) (phase : Fin 3) (who : Player) :
    quittingPeriodThreeImmediateWindow (rewardOfCoordinates first)
        (hazardOfNormalized point) phase who =
      quittingPeriodThreeImmediateWindow (rewardOfCoordinates second)
        (hazardOfNormalized point) phase who := by
  fin_cases phase <;>
    simp only [quittingPeriodThreeImmediateWindow] <;>
    rw [quittingPeriodThreeImmediateContribution_eq_of_agree_visible
        first second hagrees point,
      quittingPeriodThreeImmediateContribution_eq_of_agree_visible
        first second hagrees point,
      quittingPeriodThreeImmediateContribution_eq_of_agree_visible
        first second hagrees point]

/-- Every denominator-cleared unilateral endpoint gap is unchanged by
arbitrary changes of the four invisible reward coordinates. -/
theorem quittingPeriodThreeClearedEndpointDifference_eq_of_agree_visible
    (first second : RewardCoordinates)
    (hagrees : AgreeOnVisibleRewardCoordinates first second)
    (point : HazardCoordinate → ℝ) (phase : Fin 3) (who : Player) :
    quittingPeriodThreeClearedEndpointDifference (rewardOfCoordinates first)
        (hazardOfNormalized point) phase who =
      quittingPeriodThreeClearedEndpointDifference (rewardOfCoordinates second)
        (hazardOfNormalized point) phase who := by
  unfold quittingPeriodThreeClearedEndpointDifference
  rw [sigmaValue_eq_of_agree_visible first second hagrees point phase who,
    excludedValue_eq_of_agree_visible first second hagrees point phase who,
    quittingPeriodThreeImmediateWindow_eq_of_agree_visible
      first second hagrees point]

/-- Cleared-gap complementarity is invariant under arbitrary changes of the
four invisible reward coordinates. -/
theorem clearedGapComplementarity_of_agree_visible
    (first second : RewardCoordinates)
    (hagrees : AgreeOnVisibleRewardCoordinates first second)
    (point : HazardCoordinate → ℝ)
    (hfirst : IsQuittingPeriodThreeClearedGapComplementary
      (rewardOfCoordinates first) (hazardOfNormalized point)) :
    IsQuittingPeriodThreeClearedGapComplementary
      (rewardOfCoordinates second) (hazardOfNormalized point) := by
  intro phase who
  rw [← quittingPeriodThreeClearedEndpointDifference_eq_of_agree_visible
    first second hagrees point phase who]
  exact hfirst phase who

end GameTheory.FourPlayerOverlappingPeriodThree

end
